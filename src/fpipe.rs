#![allow(unused)]

//! Frozen Pipe for batched IO ops

use crate::{bpool, error::FrozenRes, ffile};

/// Frozen Pipe for batched IO ops
#[derive(Debug)]
pub struct FPipe {
    pool: bpool::BPool,
    file: ffile::FrozenFile,
}

impl FPipe {
    /// Create a new instance
    pub fn new(
        path: std::path::PathBuf,
        buf_size: usize,
        pool_cap: usize,
        init_cap: usize,
        module_id: u8,
    ) -> FrozenRes<Self> {
        let cfg = ffile::FFCfg {
            mid: module_id,
            chunk_size: buf_size,
            initial_chunk_amount: init_cap,
            path,
        };

        let file = ffile::FrozenFile::new(cfg)?;
        let pool = bpool::BPool::new(buf_size, pool_cap, module_id);

        Ok(Self { pool, file })
    }
}
