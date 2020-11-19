//! Transaction pool for Ethereum.

use anyhow::{anyhow, bail};
use async_trait::async_trait;
use auto_impl::auto_impl;
use ethereum::Transaction;
use ethereum_types::{Address, H256, U256};
use rlp::{Encodable, RlpStream};
use secp256k1::{
    recovery::{RecoverableSignature, RecoveryId},
    Message, SECP256K1,
};
use sha3::{Digest, Keccak256};
use std::{
    collections::{
        hash_map::Entry::{Occupied, Vacant},
        BTreeMap, HashMap, VecDeque,
    },
    convert::TryFrom,
    sync::Arc,
};
use thiserror::Error;
use tracing::*;

struct RichTransaction {
    inner: Transaction,
    sender: Address,
    hash: H256,
}

impl RichTransaction {
    fn cost(&self) -> U256 {
        self.inner.gas_limit * self.inner.gas_price + self.inner.value
    }
}

impl TryFrom<Transaction> for RichTransaction {
    type Error = anyhow::Error;

    fn try_from(tx: Transaction) -> Result<Self, Self::Error> {
        let h = {
            let mut stream = RlpStream::new();
            tx.rlp_append(&mut stream);
            Keccak256::digest(&stream.drain())
        };
        let hash = H256::from_slice(h.as_slice());

        let mut sig = [0_u8; 64];
        sig[..32].copy_from_slice(tx.signature.r().as_bytes());
        sig[32..].copy_from_slice(tx.signature.s().as_bytes());
        let rec = RecoveryId::from_i32(tx.signature.standard_v() as i32).unwrap();

        let public = &SECP256K1
            .recover(
                &Message::from_slice(
                    ethereum::TransactionMessage::from(tx.clone())
                        .hash()
                        .as_bytes(),
                )?,
                &RecoverableSignature::from_compact(&sig, rec)?,
            )?
            .serialize_uncompressed()[1..];

        let sender = Address::from_slice(&Keccak256::digest(&public)[12..]);
        Ok(Self {
            sender,
            hash,
            inner: tx,
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BlockHeader {
    hash: H256,
    parent: H256,
}

#[derive(Clone, Copy, Debug, Default)]
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

/// The necessary glue to get Ethereum state. See `Pool` docs for more info.
#[async_trait]
#[auto_impl(&, Box, Arc)]
pub trait AccountInfoProvider: Send + Sync + 'static {
    /// Get account information at specified block.
    async fn get_account_info(
        &self,
        block: H256,
        account: Address,
    ) -> anyhow::Result<Option<AccountInfo>>;
}

#[async_trait]
impl AccountInfoProvider for HashMap<H256, HashMap<Address, AccountInfo>> {
    async fn get_account_info(
        &self,
        block: H256,
        account: Address,
    ) -> anyhow::Result<Option<AccountInfo>> {
        if let Some(accounts) = self.get(&block) {
            if let Some(info) = accounts.get(&account) {
                return Ok(Some(*info));
            }
        }

        Ok(None)
    }
}

#[derive(Debug, Error)]
pub enum ImportError {
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
/// Unlike most pool implementations, this `Pool` does not support and guards against nonce gaps.
/// As a consequence, we can sort transactions by sender and store in double ended queue, where `tx_nonce = account_nonce + queue_pos`.
/// This makes traversal efficient.
///
/// `Pool` **must** be used together with a client: validity checks require knowledge about account nonce and balance.
pub struct Pool<DP: AccountInfoProvider> {
    block: BlockHeader,
    data_provider: DP,
    by_hash: HashMap<H256, Arc<RichTransaction>>,
    by_sender: HashMap<Address, AccountPool>,
}

impl<DP: AccountInfoProvider> Pool<DP> {
    /// Create a new instance of `Pool`.
    pub fn new(block: BlockHeader, data_provider: DP) -> Self {
        Self {
            block,
            data_provider,
            by_hash: Default::default(),
            by_sender: Default::default(),
        }
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

    async fn import_one_rich(&mut self, tx: Arc<RichTransaction>) -> Result<bool, ImportError> {
        match self.by_hash.entry(tx.hash) {
            Occupied(_) => {
                // Tx already there.
                Ok(false)
            }
            Vacant(tx_by_hash_entry) => {
                // This is a new transaction.
                let account_pool = match self.by_sender.entry(tx.sender) {
                    Occupied(occupied) => occupied.into_mut(),
                    Vacant(entry) => {
                        // This is a new sender, let's get its state.
                        let info = self
                            .data_provider
                            .get_account_info(self.block.hash, tx.sender)
                            .await
                            .map_err(ImportError::InvalidSender)?
                            .ok_or_else(|| {
                                ImportError::InvalidSender(anyhow!("sender account does not exist"))
                            })?;

                        entry.insert(AccountPool {
                            info,
                            txs: Default::default(),
                        })
                    }
                };

                if let Some(offset) = tx.inner.nonce.as_u64().checked_sub(account_pool.info.nonce) {
                    // This transaction's nonce is account nonce or greater.
                    if offset <= account_pool.txs.len() as u64 {
                        // This transaction is between existing txs in the pool, or right the next one.

                        // Compute balance after executing all txs before it.
                        let cumulative_balance = account_pool
                            .txs
                            .iter()
                            .take(offset as usize)
                            .fold(account_pool.info.balance, |balance, tx| balance - tx.cost());

                        // If this is a replacement transaction, pick between this and old.
                        if let Some(pooled_tx) = account_pool.txs.get_mut(offset as usize) {
                            if pooled_tx.inner.gas_price >= tx.inner.gas_price {
                                return Err(ImportError::FeeTooLow);
                            }

                            if cumulative_balance.checked_sub(tx.cost()).is_none() {
                                return Err(ImportError::InsufficientBalance);
                            }

                            tx_by_hash_entry.insert(tx.clone());
                            assert!(self.by_hash.remove(&pooled_tx.hash).is_some());
                            *pooled_tx = tx;
                        } else {
                            // Not a replacement transaction.
                            assert_eq!(tx.inner.nonce, U256::from(account_pool.txs.len()));

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
    pub async fn import_one(&mut self, tx: Transaction) -> Result<bool, ImportError> {
        let tx = Arc::new(RichTransaction::try_from(tx).map_err(ImportError::InvalidTransaction)?);

        self.import_one_rich(tx).await
    }

    /// Import several transactions.
    pub async fn import_many(
        &mut self,
        txs: Vec<Transaction>,
    ) -> HashMap<H256, Result<bool, ImportError>> {
        let txs = txs
            .into_iter()
            .filter_map(|v| RichTransaction::try_from(v).ok())
            .fold(
                HashMap::<Address, BTreeMap<U256, RichTransaction>>::new(),
                |mut txs, mut tx| {
                    match txs.entry(tx.sender).or_default().entry(tx.inner.nonce) {
                        std::collections::btree_map::Entry::Vacant(entry) => {
                            entry.insert(tx);
                        }
                        std::collections::btree_map::Entry::Occupied(mut entry) => {
                            let mut entry = entry.get_mut();

                            if tx.inner.gas_price > entry.inner.gas_price {
                                std::mem::swap(&mut tx, &mut entry);
                            }
                        }
                    };
                    txs
                },
            );

        let mut total = HashMap::with_capacity(txs.len());
        for (_, account_txs) in txs {
            let mut chain_error = false;
            for (_, tx) in account_txs {
                total.insert(
                    tx.hash,
                    if chain_error {
                        Err(ImportError::NonceGap)
                    } else {
                        let res = self.import_one_rich(Arc::new(tx)).await;

                        if res.is_err() {
                            // If we drop one account tx, then the remaining are invalid because of nonce gap.
                            chain_error = true;
                        }

                        res
                    },
                );
            }
        }

        total
    }

    /// Erase all transactions from the pool.
    pub fn erase(&mut self) {
        self.by_hash.clear();
        self.by_sender.clear();
    }

    fn apply_block_inner(
        &mut self,
        block: BlockHeader,
        account_diffs: HashMap<Address, AccountDiff>,
    ) -> anyhow::Result<()> {
        if block.parent != self.block.hash {
            bail!(
                "block gap detected: attemped to apply {} which is not child of {}",
                block.parent,
                self.block.hash
            );
        }

        for (address, account_diff) in account_diffs {
            // Only do something if we actually have pool for this sender.
            if let Occupied(mut address_entry) = self.by_sender.entry(address) {
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
        account_diffs: HashMap<Address, AccountDiff>,
    ) {
        if let Err(e) = self.apply_block_inner(block, account_diffs) {
            warn!(
                "Failed to apply block {}: {}. Resetting transaction pool.",
                block.hash, e
            );

            self.erase();
        }
        self.block = block;
    }

    fn revert_block_inner(
        &mut self,
        block: BlockHeader,
        _reverted_txs: Vec<Transaction>,
    ) -> anyhow::Result<()> {
        if self.block.parent != block.hash {
            bail!(
                "block gap detected: attempted to revert to {}, expected {}",
                block.hash,
                self.block.parent
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
        self.block = block;
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
    use hex_literal::hex;

    #[test]
    fn test_parse_transaction() {
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
}
