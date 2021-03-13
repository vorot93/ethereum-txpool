//! Transaction pool for Ethereum.

use anyhow::{anyhow, bail};
use ethereum::Transaction;
use ethereum_types::{Address, H256, U256};
use rlp::{Encodable, RlpStream};
use secp256k1::{
    recovery::{RecoverableSignature, RecoveryId},
    Message, PublicKey, SECP256K1,
};
use sha3::{Digest, Keccak256};
use std::{
    collections::{
        hash_map::Entry::{Occupied, Vacant},
        BTreeMap, HashMap, VecDeque,
    },
    convert::{TryFrom, TryInto},
    sync::Arc,
};
use thiserror::Error;
use tracing::*;

struct RichTransaction {
    inner: Transaction,
    sender: Address,
    hash: H256,
    // temporary crutch
    nonce: u64,
}

impl RichTransaction {
    fn cost(&self) -> U256 {
        self.inner.gas_limit * self.inner.gas_price + self.inner.value
    }
}

fn pk2addr(pk: &PublicKey) -> Address {
    Address::from_slice(&Keccak256::digest(&pk.serialize_uncompressed()[1..])[12..])
}

impl TryFrom<Transaction> for RichTransaction {
    type Error = anyhow::Error;

    fn try_from(tx: Transaction) -> Result<Self, Self::Error> {
        let h = {
            let mut stream = RlpStream::new();
            tx.rlp_append(&mut stream);
            Keccak256::digest(&stream.out())
        };
        let hash = H256::from_slice(h.as_slice());

        let mut sig = [0_u8; 64];
        sig[..32].copy_from_slice(tx.signature.r().as_bytes());
        sig[32..].copy_from_slice(tx.signature.s().as_bytes());
        let rec = RecoveryId::from_i32(tx.signature.standard_v() as i32).unwrap();

        let public = &SECP256K1.recover(
            &Message::from_slice(
                ethereum::TransactionMessage::from(tx.clone())
                    .hash()
                    .as_bytes(),
            )?,
            &RecoverableSignature::from_compact(&sig, rec)?,
        )?;

        Ok(Self {
            sender: pk2addr(public),
            hash,
            nonce: tx
                .nonce
                .try_into()
                .map_err(|e| anyhow!("invalid nonce: {}", e))?,
            inner: tx,
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BlockHeader {
    pub hash: H256,
    pub parent: H256,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct AccountInfo {
    pub balance: U256,
    pub nonce: u64,
}

/// Account diff
#[derive(Clone, Copy, Debug)]
pub enum AccountDiff {
    Changed(AccountInfo),
    Deleted,
}

#[derive(Debug, Error)]
pub enum ImportError {
    #[error("need state for account: {0}")]
    NoState(Address),
    #[error("invalid transaction: {0}")]
    InvalidTransaction(anyhow::Error),
    #[error("nonce gap")]
    NonceGap,
    #[error("stale transaction")]
    StaleTransaction,
    #[error("invalid sender: {0}")]
    InvalidSender(anyhow::Error),
    #[error("fee too low")]
    FeeTooLow,
    #[error("not enough balance to pay for gas")]
    InsufficientBalance,
    #[error("current block has not been set")]
    NoCurrentBlock,
    #[error("other: {0}")]
    Other(anyhow::Error),
}

#[derive(Clone, Copy, Debug)]
pub struct Status {
    pub transactions: usize,
    pub senders: usize,
}

struct AccountPool {
    info: AccountInfo,
    txs: VecDeque<Arc<RichTransaction>>,
}

impl AccountPool {
    fn prune_insufficient_balance(
        &mut self,
        cache: Option<(usize, U256)>,
    ) -> VecDeque<Arc<RichTransaction>> {
        let (offset, mut cumulative_balance) = cache.unwrap_or((0, self.info.balance));

        for (i, tx) in self.txs.iter().enumerate().skip(offset as usize) {
            if let Some(balance) = cumulative_balance.checked_sub(tx.cost()) {
                cumulative_balance = balance;
            } else {
                return self.txs.split_off(i);
            }
        }

        VecDeque::new()
    }
}

/// Transaction pool that is able to import Ethereum transactions, check their validity and provide traversal over all of them.
///
/// Unlike most pool implementations, [Pool] does not support and guards against nonce gaps.
/// As a consequence, we can sort transactions by sender and store in double ended queue, where `tx_nonce = account_nonce + queue_pos`.
/// This makes traversal efficient.
///
/// [Pool] **must** be used together with a client: validity checks require knowledge about account nonce and balance.
#[derive(Default)]
pub struct Pool {
    block: Option<BlockHeader>,
    by_hash: HashMap<H256, Arc<RichTransaction>>,
    by_sender: HashMap<Address, AccountPool>,
}

impl Pool {
    /// Create a new pool instance.
    pub fn new() -> Self {
        Default::default()
    }

    /// Get status of this pool.
    pub fn status(&self) -> Status {
        Status {
            transactions: self.by_hash.len(),
            senders: self.by_sender.len(),
        }
    }

    /// Get transaction by its hash.
    pub fn get(&self, hash: H256) -> Option<&Transaction> {
        self.by_hash.get(&hash).map(|tx| &tx.inner)
    }

    fn import_one_rich(&mut self, tx: Arc<RichTransaction>) -> Result<bool, ImportError> {
        self.block.ok_or(ImportError::NoCurrentBlock)?;

        match self.by_hash.entry(tx.hash) {
            Occupied(_) => {
                // Tx already there.
                Ok(false)
            }
            Vacant(tx_by_hash_entry) => {
                // This is a new transaction.
                let account_pool = self
                    .by_sender
                    .get_mut(&tx.sender)
                    .ok_or(ImportError::NoState(tx.sender))?;

                if let Some(offset) = tx.nonce.checked_sub(account_pool.info.nonce) {
                    // This transaction's nonce is account nonce or greater.
                    if offset <= account_pool.txs.len() as u64 {
                        // This transaction is between existing txs in the pool, or right the next one.

                        // Compute balance after executing all txs before it.
                        let cumulative_balance = account_pool
                            .txs
                            .iter()
                            .take(offset as usize)
                            .fold(account_pool.info.balance, |balance, tx| balance - tx.cost());

                        if cumulative_balance.checked_sub(tx.cost()).is_none() {
                            return Err(ImportError::InsufficientBalance);
                        }

                        // If this is a replacement transaction, pick between this and old.
                        if let Some(pooled_tx) = account_pool.txs.get_mut(offset as usize) {
                            if pooled_tx.inner.gas_price >= tx.inner.gas_price {
                                return Err(ImportError::FeeTooLow);
                            }

                            tx_by_hash_entry.insert(tx.clone());
                            assert!(self.by_hash.remove(&pooled_tx.hash).is_some());
                            *pooled_tx = tx;
                        } else {
                            // Not a replacement transaction.
                            assert_eq!(tx.nonce, account_pool.txs.len() as u64);

                            tx_by_hash_entry.insert(tx.clone());
                            account_pool.txs.push_back(tx);
                        }

                        // Compute the balance after executing remaining transactions. Select for removal those for which we do not have enough balance.
                        for tx in account_pool
                            .prune_insufficient_balance(Some((offset as usize, cumulative_balance)))
                        {
                            assert!(self.by_hash.remove(&tx.hash).is_some());
                        }

                        Ok(true)
                    } else {
                        Err(ImportError::NonceGap)
                    }
                } else {
                    // Nonce lower than account, meaning it's stale.
                    Err(ImportError::StaleTransaction)
                }
            }
        }
    }

    /// Import one transaction.
    pub fn import_one(&mut self, tx: Transaction) -> Result<bool, ImportError> {
        let tx = Arc::new(RichTransaction::try_from(tx).map_err(ImportError::InvalidTransaction)?);

        self.import_one_rich(tx)
    }

    /// Import several transactions.
    pub fn import_many(
        &mut self,
        txs: impl Iterator<Item = Transaction>,
    ) -> Vec<Result<bool, ImportError>> {
        let mut out = vec![];

        let txs = txs.enumerate().fold(
            HashMap::<Address, BTreeMap<u64, (usize, RichTransaction)>>::new(),
            |mut txs, (idx, tx)| {
                out.push(Ok(false));
                match RichTransaction::try_from(tx) {
                    Err(e) => {
                        out[idx] = Err(ImportError::InvalidTransaction(e));
                        txs
                    }
                    Ok(tx) => {
                        match txs.entry(tx.sender).or_default().entry(tx.nonce) {
                            std::collections::btree_map::Entry::Vacant(entry) => {
                                entry.insert((idx, tx));
                            }
                            std::collections::btree_map::Entry::Occupied(mut entry) => {
                                let (old_idx, old_tx) = entry.get();

                                if tx.inner.gas_price > old_tx.inner.gas_price {
                                    out[*old_idx] = Err(ImportError::FeeTooLow);
                                    *entry.get_mut() = (idx, tx);
                                } else {
                                    out[idx] = Err(ImportError::FeeTooLow);
                                }
                            }
                        };
                        txs
                    }
                }
            },
        );

        for (_sender, account_txs) in txs {
            let mut chain_error = false;
            let mut no_state = None;
            for (_nonce, (idx, tx)) in account_txs {
                out[idx] = {
                    if chain_error {
                        Err({
                            if let Some(address) = no_state {
                                ImportError::NoState(address)
                            } else {
                                ImportError::NonceGap
                            }
                        })
                    } else {
                        let res = self.import_one_rich(Arc::new(tx));

                        if let Err(e) = &res {
                            // If we drop one account tx, then the remaining are invalid because of nonce gap.
                            chain_error = true;

                            if let ImportError::NoState(address) = e {
                                no_state = Some(*address);
                            }
                        }

                        res
                    }
                };
            }
        }

        out
    }

    /// Get current block this pool is at.
    pub fn current_block(&self) -> Option<BlockHeader> {
        self.block
    }

    /// Erase all transactions from the pool.
    pub fn erase(&mut self) {
        self.by_hash.clear();
        self.by_sender.clear();
    }

    /// Reset transaction pool to this block.
    pub fn reset(&mut self, block: Option<BlockHeader>) {
        self.erase();
        self.block = block;
    }

    /// Add state of the account to this pool.
    pub fn add_account_state(&mut self, address: Address, info: AccountInfo) -> bool {
        if let Vacant(entry) = self.by_sender.entry(address) {
            entry.insert(AccountPool {
                info,
                txs: Default::default(),
            });

            return true;
        }

        false
    }

    /// Drop account from this pool.
    pub fn drop_account(&mut self, address: Address) -> bool {
        if let Some(pool) = self.by_sender.remove(&address) {
            for tx in pool.txs {
                assert!(self.by_hash.remove(&tx.hash).is_some());
            }
            return true;
        }

        false
    }

    /// Get account state in this pool.
    pub fn account_state(&self, address: Address) -> Option<AccountInfo> {
        self.by_sender.get(&address).map(|pool| pool.info)
    }

    fn apply_block_inner(
        &mut self,
        block: BlockHeader,
        account_diffs: &HashMap<Address, AccountDiff>,
    ) -> anyhow::Result<()> {
        let current_block = if let Some(b) = self.block {
            b
        } else {
            return Ok(());
        };

        if block.parent != current_block.hash {
            bail!(
                "block gap detected: attempted to apply {} which is not child of {}",
                block.parent,
                current_block.hash
            );
        }

        for (address, account_diff) in account_diffs {
            // Only do something if we actually have pool for this sender.
            if let Occupied(mut address_entry) = self.by_sender.entry(*address) {
                match account_diff {
                    AccountDiff::Changed(new_info) => {
                        let pool = address_entry.get_mut();
                        let nonce_diff = new_info
                            .nonce
                            .checked_sub(pool.info.nonce)
                            .ok_or_else(|| anyhow!("nonce can only move forward!"))?;

                        for _ in 0..nonce_diff {
                            if let Some(tx) = pool.txs.pop_front() {
                                assert!(self.by_hash.remove(&tx.hash).is_some());
                            }
                        }

                        // update info
                        pool.info = *new_info;
                        // More expensive tx could have squeezed in - we have to recheck our balance.
                        for tx in pool.prune_insufficient_balance(None) {
                            assert!(self.by_hash.remove(&tx.hash).is_some());
                        }

                        if pool.txs.is_empty() {
                            address_entry.remove();
                        }
                    }
                    AccountDiff::Deleted => {
                        for tx in address_entry.remove().txs {
                            assert!(self.by_hash.remove(&tx.hash).is_some());
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Apply state updates from new confirmed block.
    /// This should be called by the client when it confirms new block.
    pub fn apply_block(
        &mut self,
        block: BlockHeader,
        account_diffs: &HashMap<Address, AccountDiff>,
    ) {
        if let Err(e) = self.apply_block_inner(block, account_diffs) {
            warn!(
                "Failed to apply block {}: {}. Resetting transaction pool.",
                block.hash, e
            );

            self.erase();
        }
        self.block = Some(block);
    }

    fn revert_block_inner(
        &mut self,
        block: BlockHeader,
        _reverted_txs: Vec<Transaction>,
    ) -> anyhow::Result<()> {
        let current_block = if let Some(b) = self.block {
            b
        } else {
            return Ok(());
        };

        if current_block.parent != block.hash {
            bail!(
                "block gap detected: attempted to revert to {}, expected {}",
                block.hash,
                current_block.parent
            );
        }

        Err(anyhow!("not implemented"))
    }

    /// Revert state updates from block that has become non-canonical, restore its transactions to the pool.
    /// This should be called by the client when it encounters a reorg.
    pub fn revert_block(&mut self, block: BlockHeader, reverted_txs: Vec<Transaction>) {
        if let Err(e) = self.revert_block_inner(block, reverted_txs) {
            warn!(
                "Failed to revert block {}: {}. Resetting transaction pool.",
                block.hash, e
            );

            self.erase();
        }
        self.block = Some(block);
    }

    /// Produce an iterator over all pending transactions in random order.
    pub fn pending_transactions(&self) -> impl Iterator<Item = &Transaction> {
        self.by_hash.values().map(|tx| &tx.inner)
    }

    /// Produce an iterator for pending transactions from `sender`, sorted by nonce in ascending order.
    pub fn pending_transactions_for_sender(
        &self,
        sender: Address,
    ) -> Option<impl Iterator<Item = &Transaction>> {
        self.by_sender
            .get(&sender)
            .map(|pool| pool.txs.iter().map(|tx| &tx.inner))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ethereum::{TransactionAction, TransactionMessage, TransactionSignature};
    use hex_literal::hex;
    use maplit::hashmap;
    use secp256k1::SecretKey;
    use std::iter::repeat_with;

    const CHAIN_ID: u64 = 1;

    const B_0: BlockHeader = BlockHeader {
        parent: H256(hex!(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
        )),
        hash: H256(hex!(
            "0000000000000000000000000000000000000000000000000000000000000000"
        )),
    };

    const B_1: BlockHeader = BlockHeader {
        parent: H256(hex!(
            "0000000000000000000000000000000000000000000000000000000000000000"
        )),
        hash: H256(hex!(
            "0000000000000000000000000000000000000000000000000000000000000001"
        )),
    };

    fn cost(tx: &TransactionMessage) -> U256 {
        tx.gas_limit * tx.gas_price + tx.value
    }

    fn sign_tx(secret_key: &SecretKey, transaction_message: TransactionMessage) -> Transaction {
        let (rec, sig) = SECP256K1
            .sign_recoverable(
                &Message::from_slice(transaction_message.hash().as_bytes()).unwrap(),
                &secret_key,
            )
            .serialize_compact();

        let mut v = rec.to_i32() as u64;

        v += if let Some(n) = transaction_message.chain_id {
            35 + n * 2
        } else {
            27
        };

        Transaction {
            nonce: transaction_message.nonce,
            gas_price: transaction_message.gas_price,
            gas_limit: transaction_message.gas_limit,
            action: transaction_message.action,
            value: transaction_message.value,
            input: transaction_message.input,
            signature: TransactionSignature::new(
                v,
                H256::from_slice(&sig[..32]),
                H256::from_slice(&sig[32..]),
            )
            .unwrap(),
        }
    }

    fn sk2addr(sk: &SecretKey) -> Address {
        pk2addr(&PublicKey::from_secret_key(SECP256K1, &sk))
    }

    fn fixture() -> (Pool, Vec<SecretKey>) {
        let s = repeat_with(|| SecretKey::new(&mut secp256k1::rand::thread_rng()))
            .take(3)
            .collect::<Vec<_>>();

        let txs = vec![
            TransactionMessage {
                nonce: 0.into(),
                gas_limit: 100000.into(),
                gas_price: 100000.into(),
                action: TransactionAction::Create,
                value: 0.into(),
                input: vec![],
                chain_id: Some(CHAIN_ID),
            },
            TransactionMessage {
                nonce: 1.into(),
                gas_limit: 50000.into(),
                gas_price: 50000.into(),
                action: TransactionAction::Create,
                value: 0.into(),
                input: vec![],
                chain_id: Some(CHAIN_ID),
            },
            TransactionMessage {
                nonce: 2.into(),
                gas_limit: 2000000.into(),
                gas_price: 10000.into(),
                action: TransactionAction::Create,
                value: 0.into(),
                input: vec![],
                chain_id: Some(CHAIN_ID),
            },
        ];

        let total_cost = txs.iter().fold(U256::zero(), |sum, tx| sum + cost(tx));
        let base_account_info = AccountInfo {
            nonce: 0,
            balance: total_cost,
        };

        let base_state = hashmap! {
            sk2addr(&s[0]) => base_account_info,
            sk2addr(&s[1]) => base_account_info,
            sk2addr(&s[2]) => base_account_info,
        };

        let mut pool = Pool::new();
        pool.reset(Some(B_0));

        for (&address, &state) in &base_state {
            pool.add_account_state(address, state);
        }

        for sk in &s {
            for tx in &txs {
                let tx = sign_tx(sk, tx.clone());
                let rich_tx = RichTransaction::try_from(tx.clone()).unwrap();
                assert_eq!(rich_tx.sender, sk2addr(sk));
                println!("signing and importing {}/{}", sk, rich_tx.hash);
                assert!(pool.import_one(tx).unwrap());
            }
        }

        (pool, s)
    }

    #[test]
    fn parse_transaction() {
        let raw = hex!("f86e821d82850525dbd38082520894ce96e38eeff1c972f8f2851a7275b79b13b9a0498805e148839955f4008025a0ab1d3780cf338d1f86f42181ed13cd6c7fee7911a942c7583d36c9c83f5ec419a04984933928fac4b3242b9184aed633cc848f6a11d42af743f262ccf6592b8f71");

        let res = RichTransaction::try_from(rlp::decode::<Transaction>(&raw).unwrap()).unwrap();

        assert_eq!(
            &hex::encode(res.hash.0),
            "560ab39fe63d8fbbf688f0ebb6cfcacee4ce2ae8d85b096aa04c22a7c4c438af"
        );

        assert_eq!(
            &hex::encode(res.sender.as_bytes()),
            "3123c4396f1306678f382c186aee2dccce44f72c"
        );
    }

    #[test]
    fn basic() {
        fixture();
    }

    #[test]
    fn import_multiple() {
        let (pool, sk) = fixture();

        let mut new_pool = Pool::new();
        new_pool.reset(pool.current_block());
        for sk in &sk {
            let address = sk2addr(sk);
            assert!(new_pool.add_account_state(address, pool.account_state(address).unwrap()))
        }

        for res in new_pool.import_many(pool.pending_transactions().cloned()) {
            assert!(res.unwrap())
        }
    }

    #[test]
    fn replace_transaction() {
        let (mut pool, sk) = fixture();

        let sk = &sk[0];

        let mut new_pool_txs = pool
            .pending_transactions_for_sender(sk2addr(sk))
            .unwrap()
            .cloned()
            .collect::<Vec<_>>();

        // No balance for this one
        new_pool_txs.pop().unwrap();

        let replaced_tx = new_pool_txs.pop().unwrap();

        let replacement = sign_tx(
            sk,
            TransactionMessage {
                nonce: replaced_tx.nonce,
                gas_price: replaced_tx.gas_price + 1,
                gas_limit: replaced_tx.gas_limit,
                action: replaced_tx.action,
                value: replaced_tx.value,
                input: replaced_tx.input,
                chain_id: Some(CHAIN_ID),
            },
        );

        new_pool_txs.push(replacement.clone());

        assert!(pool.import_one(replacement).unwrap());

        assert_eq!(
            new_pool_txs,
            pool.pending_transactions_for_sender(sk2addr(sk))
                .unwrap()
                .cloned()
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn apply_block() {
        let (mut pool, sk) = fixture();

        let mut account_infos = HashMap::new();
        for sk in &sk {
            let mut pool_txs = pool
                .pending_transactions_for_sender(sk2addr(sk))
                .unwrap()
                .cloned()
                .collect::<Vec<_>>();

            let last_tx: Transaction = pool_txs.pop().unwrap();

            let new_info = AccountInfo {
                nonce: last_tx.nonce.as_u64().checked_sub(1).unwrap_or_default(),
                balance: cost(&last_tx.into()),
            };
            account_infos.insert(sk2addr(sk), new_info);
        }

        pool.apply_block(
            B_1,
            &account_infos
                .iter()
                .map(|(&addr, &state)| (addr, AccountDiff::Changed(state)))
                .collect(),
        );

        for (address, new_info) in account_infos {
            assert_eq!(pool.account_state(address).unwrap(), new_info);
        }
    }
}
