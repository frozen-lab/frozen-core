//! An high throughput asynchronous IO pipeline for chunk based storage, it uses batches to write requests and
//! flushes them in the background, while providing durability guarantees via epochs
//!
//! `FrozenPipe` batches write requests and flushes them in the background, providing durability guarantees via epochs
//!
//! ## Features
//!
//! - Batched IO
//! - Background durability
//! - Backpressure via [`BufPool`]
//! - Crash-safe durability semantics
//! - Optimized page reads
//!
//! ## Example
//!
//! ```
//! use frozen_core::fpipe::{FrozenPipe, FPCfg};
//! use frozen_core::bpool::BPBackend;
//! use std::time::Duration;
//!
//! const MODULE_ID: u8 = 0;
//!
//! let dir = tempfile::tempdir().unwrap();
//! let path = dir.path().join("tmp_pipe");
//!
//! let cfg = FPCfg {
//!     chunk_size: 0x20,
//!     initial_chunk_amount: 4,
//!     flush_duration: Duration::from_micros(0x3A),
//!     backend: BPBackend::Prealloc { capacity: 0x10 },
//! };
//!
//! let pipe = FrozenPipe::<MODULE_ID>::new(path, cfg).unwrap();
//!
//! let data = vec![1u8; 0x40];
//! let bufs = vec![
//!     &data[0x00..0x20],
//!     &data[0x20..0x40],
//! ];
//!
//! let epoch = unsafe { pipe.write(&bufs, 0) }.unwrap();
//! pipe.wait_for_durability(epoch).unwrap();
//!
//! let read = pipe.read(0, 2).unwrap();
//! assert_eq!(read, data);
//! ```

use crate::{
    bpool,
    error::{ErrCode, FrozenErr, FrozenRes},
    ffile, hints, mpscq,
};
use std::{
    sync::{self, atomic},
    thread, time,
};

/// Domain Id for [`FrozenPipe`] is **20**
const ERRDOMAIN: u8 = 0x14;

/// module id used for [`FrozenErr`]
static MID: std::sync::OnceLock<u8> = std::sync::OnceLock::new();

#[inline(always)]
fn mid() -> &'static u8 {
    MID.get().unwrap()
}

/// Error codes for [`FrozenPipe`]
mod err {
    use super::ErrCode;

    /// (1024) flush_tx error (panic inside)
    pub const TXE: ErrCode = ErrCode::new(0x400, "flush_tx paniced inside");

    /// (1025) flush_tx error (unable to spawn)
    pub const FXE: ErrCode = ErrCode::new(0x401, "unable to spawn flush_tx");

    /// (1026) lock poisoned
    pub const LPN: ErrCode = ErrCode::new(0x402, "lock poisoned internally");
}

#[inline]
fn new_err<R, E: std::fmt::Display>(code: ErrCode, error: E) -> FrozenRes<R> {
    let err = FrozenErr::new_raw(*mid(), ERRDOMAIN, code, error);
    Err(err)
}

#[inline]
fn new_err_raw<E: std::fmt::Display>(code: ErrCode, error: E) -> FrozenErr {
    FrozenErr::new_raw(*mid(), ERRDOMAIN, code, error)
}

/// Config for [`FrozenPipe`]
#[derive(Debug, Clone)]
pub struct FPCfg {
    /// Backend used [`BufPool`]
    pub backend: bpool::BPBackend,

    /// Size (in bytes) of a single chunk on fs
    ///
    /// A chunk is a smalled fixed size allocation and addressing unit used by
    /// [`FrozenFile`] for all the write/read ops, which are operated by index
    /// of the chunk and not the offset of the byte
    pub chunk_size: usize,

    /// Number of chunks to pre-allocate when [`FrozenFile`] is initialized
    ///
    /// Initial file length will be `chunk_size * initial_chunk_amount` (bytes)
    pub initial_chunk_amount: usize,

    /// Time interval used by flusher tx, to batch write ops into a durable window and sync them
    /// together, where all write ops in certain time interval falls into a single durable window
    pub flush_duration: time::Duration,
}

/// An high throughput asynchronous IO pipeline for chunk based storage, it uses batches to write requests and
/// flushes them in the background, while providing durability guarantees via epochs
///
/// ## Example
///
/// ```
/// use frozen_core::fpipe::{FrozenPipe, FPCfg};
/// use frozen_core::bpool::BPBackend;
/// use std::time::Duration;
///
/// const MODULE_ID: u8 = 0;
///
/// let dir = tempfile::tempdir().unwrap();
/// let path = dir.path().join("tmp_pipe_write");
///
/// let cfg = FPCfg {
///     chunk_size: 0x20,
///     initial_chunk_amount: 2,
///     backend: BPBackend::Dynamic,
///     flush_duration: Duration::from_micros(0x3A),
/// };
///
/// let pipe = FrozenPipe::<MODULE_ID>::new(path, cfg).unwrap();
///
/// let data = vec![1u8; 0x40];
/// let bufs = vec![
///     &data[0x00..0x20],
///     &data[0x20..0x40],
/// ];
///
/// let epoch = unsafe { pipe.write(&bufs, 0) }.unwrap();
/// pipe.wait_for_durability(epoch).unwrap();
///
/// let read = pipe.read(0, 2).unwrap();
/// assert_eq!(read, data);
/// ```
#[derive(Debug)]
pub struct FrozenPipe<const MODULE_ID: u8> {
    core: sync::Arc<Core>,
    tx: Option<thread::JoinHandle<()>>,
}

unsafe impl<const MODULE_ID: u8> Send for FrozenPipe<MODULE_ID> {}
unsafe impl<const MODULE_ID: u8> Sync for FrozenPipe<MODULE_ID> {}

impl<const MODULE_ID: u8> FrozenPipe<MODULE_ID> {
    /// Create a new instance of [`FrozenPipe`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fpipe::{FrozenPipe, FPCfg};
    /// use frozen_core::bpool::BPBackend;
    /// use std::time::Duration;
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_pipe_write");
    ///
    /// let cfg = FPCfg {
    ///     chunk_size: 0x20,
    ///     initial_chunk_amount: 2,
    ///     backend: BPBackend::Dynamic,
    ///     flush_duration: Duration::from_micros(0x3A),
    /// };
    ///
    /// let pipe = FrozenPipe::<MODULE_ID>::new(path, cfg).unwrap();
    ///
    /// let data = vec![1u8; 0x20];
    /// let bufs = vec![&data[0x00..0x20]];
    ///
    /// let epoch = unsafe { pipe.write(&bufs, 0) }.unwrap();
    /// pipe.wait_for_durability(epoch).unwrap();
    ///
    /// let read = pipe.read(0, 1).unwrap();
    /// assert_eq!(read, data);
    /// ```
    pub fn new<P: AsRef<std::path::Path>>(path: P, cfg: FPCfg) -> FrozenRes<Self> {
        let file = ffile::FrozenFile::new::<MODULE_ID>(ffile::FFCfg {
            path: path.as_ref().to_path_buf(),
            chunk_size: cfg.chunk_size,
            initial_chunk_amount: cfg.initial_chunk_amount,
        })?;
        let pool = bpool::BufPool::new::<MODULE_ID>(bpool::BPCfg {
            chunk_size: cfg.chunk_size,
            backend: cfg.backend,
        });

        // NOTE: The value is used for error logging and is initialized only once, as `OnceLock` guarantees that the
        // first caller sets the value and all subsequent calls reuse it
        let _ = MID.get_or_init(|| MODULE_ID);

        let core = Core::new(file, pool, cfg)?;

        // INFO: we spawn the thread for background sync
        let tx = Core::spawn_tx(core.clone())?;

        Ok(Self { core, tx: Some(tx) })
    }

    /// Submit a write request
    ///
    /// ## Working
    ///
    /// The buffer is split into `chunk_size` sized segments and staged using [`BufPool`] before being
    /// written by the background flusher
    ///
    /// Returns the epoch representing the durability window of the write
    ///
    /// ## Requirements
    ///
    /// Length of each data buffer in given `&[buf]` must be of exact `chunk_size`, otherwise the call may cause
    /// undefined behaviour
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fpipe::{FrozenPipe, FPCfg};
    /// use frozen_core::bpool::BPBackend;
    /// use std::time::Duration;
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_pipe_write");
    ///
    /// let cfg = FPCfg {
    ///     chunk_size: 0x20,
    ///     initial_chunk_amount: 2,
    ///     backend: BPBackend::Dynamic,
    ///     flush_duration: Duration::from_micros(0x3A),
    /// };
    ///
    /// let pipe = FrozenPipe::<MODULE_ID>::new(path, cfg).unwrap();
    ///
    /// let data = [0x3Bu8; 0x40];
    /// let bufs = vec![
    ///     &data[0x00..0x20],
    ///     &data[0x20..0x40],
    /// ];
    ///
    /// let epoch = unsafe { pipe.write(&bufs, 0) }.unwrap();
    /// pipe.wait_for_durability(epoch).unwrap();
    ///
    /// let read = pipe.read(0, 2).unwrap();
    /// assert_eq!(read, data);
    /// ```
    #[inline(always)]
    pub unsafe fn write(&self, buf: &[&[u8]], index: usize) -> FrozenRes<u64> {
        if let Some(err) = self.core.get_sync_error() {
            return Err(err);
        }

        let chunk_size = self.core.cfg.chunk_size;
        let chunks = buf.len();

        let alloc = self.core.pool.allocate(chunks)?;

        // NOTE: Read lock prevents torn syncs by ensuring the flusher_tx cannot acquire an exclusive lock unitl the
        // write ops is submited, while this lock must be acquired after pool allocations as `BufPool::allocate` may
        // block while waiting for chunks, otherwise the wait would delay the flusher from obtaining the lock, and
        // potentially stalling the durability progress for the entire `FrozenPipe`
        let _lock = self.core.acquire_io_lock()?;

        for (idx, ptr) in alloc.slots().iter().enumerate() {
            unsafe {
                std::ptr::copy_nonoverlapping(buf[idx].as_ptr(), *ptr, chunk_size);
            };
        }

        let epoch = self.core.epoch.load(atomic::Ordering::Acquire);
        let req = WriteReq::new(index, chunks, alloc);
        self.core.mpscq.push(req);

        Ok(epoch)
    }

    /// Read a single chunk from the given `index`
    ///
    /// This function performs a blocking read operation
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fpipe::{FrozenPipe, FPCfg};
    /// use frozen_core::bpool::BPBackend;
    /// use std::time::Duration;
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_pipe_write");
    ///
    /// let cfg = FPCfg {
    ///     chunk_size: 0x20,
    ///     initial_chunk_amount: 2,
    ///     backend: BPBackend::Dynamic,
    ///     flush_duration: Duration::from_micros(0x3A),
    /// };
    ///
    /// let pipe = FrozenPipe::<MODULE_ID>::new(path, cfg).unwrap();
    ///
    /// let data = vec![0xAAu8; 0x20];
    /// let bufs = vec![&data[0x00..0x20]];
    ///
    /// let epoch = unsafe { pipe.write(&bufs, 0) }.unwrap();
    /// pipe.wait_for_durability(epoch).unwrap();
    ///
    /// let read = pipe.read_single(0).unwrap();
    /// assert_eq!(read, data);
    /// ```
    #[inline(always)]
    pub fn read_single(&self, index: usize) -> FrozenRes<Vec<u8>> {
        let _lock = self.core.acquire_io_lock()?;

        let mut slice = vec![0u8; self.core.cfg.chunk_size];
        self.core.file.pread(slice.as_mut_ptr(), index)?;

        drop(_lock);
        Ok(slice)
    }

    /// Read `count` chunks starting from at the given `index`
    ///
    /// This function performs a blocking read operation
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fpipe::{FrozenPipe, FPCfg};
    /// use frozen_core::bpool::BPBackend;
    /// use std::time::Duration;
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_pipe_write");
    ///
    /// let cfg = FPCfg {
    ///     chunk_size: 0x20,
    ///     initial_chunk_amount: 2,
    ///     backend: BPBackend::Dynamic,
    ///     flush_duration: Duration::from_micros(0x3A),
    /// };
    ///
    /// let pipe = FrozenPipe::<MODULE_ID>::new(path, cfg).unwrap();
    ///
    /// let data = vec![0xBBu8; 0x20 * 2];
    /// let bufs = vec![&data[0x00..0x20], &data[0x20..0x40]];
    ///
    /// let epoch = unsafe { pipe.write(&bufs, 0) }.unwrap();
    /// pipe.wait_for_durability(epoch).unwrap();
    ///
    /// let read = pipe.read(0, 2).unwrap();
    /// assert_eq!(read, data);
    /// ```
    #[inline(always)]
    pub fn read(&self, index: usize, count: usize) -> FrozenRes<Vec<u8>> {
        let _lock = self.core.acquire_io_lock()?;

        match count {
            2 => self.read_2x(index),
            4 => self.read_4x(index),
            _ => self.read_multi(index, count),
        }
    }

    /// Blocks until given `epoch` becomes durable
    ///
    /// Durability epochs increase when the background flusher successfully syncs the underlying [`FrozenFile`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fpipe::{FrozenPipe, FPCfg};
    /// use frozen_core::bpool::BPBackend;
    /// use std::time::Duration;
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_pipe_write");
    ///
    /// let cfg = FPCfg {
    ///     chunk_size: 0x20,
    ///     initial_chunk_amount: 2,
    ///     backend: BPBackend::Dynamic,
    ///     flush_duration: Duration::from_micros(0x3A),
    /// };
    ///
    /// let pipe = FrozenPipe::<MODULE_ID>::new(path, cfg).unwrap();
    ///
    /// let data = vec![1u8; 0x20];
    /// let bufs = vec![&data[0x00..0x20]];
    ///
    /// let epoch = unsafe { pipe.write(&bufs, 0) }.unwrap();
    /// pipe.wait_for_durability(epoch).unwrap();
    /// ```
    pub fn wait_for_durability(&self, epoch: u64) -> FrozenRes<()> {
        self.internal_wait(epoch)
    }

    /// Force instant durability for the current batch
    ///
    /// This wakes the flusher thread and waits for the durability epoch
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fpipe::{FrozenPipe, FPCfg};
    /// use frozen_core::bpool::BPBackend;
    /// use std::time::Duration;
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_pipe_write");
    ///
    /// let cfg = FPCfg {
    ///     chunk_size: 0x20,
    ///     initial_chunk_amount: 2,
    ///     backend: BPBackend::Dynamic,
    ///     flush_duration: Duration::from_micros(0x3A),
    /// };
    ///
    /// let pipe = FrozenPipe::<MODULE_ID>::new(path, cfg).unwrap();
    ///
    /// let data = vec![1u8; 0x20];
    /// let bufs = vec![&data[0x00..0x20]];
    ///
    /// let epoch = unsafe { pipe.write(&bufs, 0) }.unwrap();
    /// pipe.force_durability(epoch).unwrap();
    /// ```
    pub fn force_durability(&self, epoch: u64) -> FrozenRes<()> {
        let guard = self.core.lock.lock().map_err(|e| new_err_raw(err::LPN, e))?;
        self.core.cv.notify_one();
        drop(guard);

        self.internal_wait(epoch)
    }

    /// Grow the underlying [`FrozenFile`] by given `count`
    ///
    /// The pipeline waits until all pending writes are flushed before extending the file
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fpipe::{FrozenPipe, FPCfg};
    /// use frozen_core::bpool::BPBackend;
    /// use std::time::Duration;
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_pipe_write");
    ///
    /// let cfg = FPCfg {
    ///     chunk_size: 0x20,
    ///     initial_chunk_amount: 0x0A,
    ///     backend: BPBackend::Dynamic,
    ///     flush_duration: Duration::from_micros(0x3A),
    /// };
    ///
    /// let pipe = FrozenPipe::<MODULE_ID>::new(path, cfg).unwrap();
    /// pipe.grow(0x0A).unwrap();
    ///
    /// let total_chunks = pipe.total_chunks().unwrap();
    /// assert_eq!(total_chunks, 0x14);
    /// ```
    pub fn grow(&self, count: usize) -> FrozenRes<()> {
        loop {
            // NOTE: we must make sure there are no remaining items in the queue left for sync
            if hints::likely(!self.core.mpscq.is_empty()) {
                let epoch = self.core.epoch.load(atomic::Ordering::Acquire);
                self.force_durability(epoch)?;
            }

            // we acquire an exclusive lock to block write, read and sync ops
            let lock = self.core.acquire_exclusive_io_lock()?;

            // NOTE: it is possible that a write could sneak in between the sync and lock acquire, if so we must
            // make sure that it has synced

            if self.core.mpscq.is_empty() {
                self.core.file.grow(count)?;
                drop(lock);
                return Ok(());
            }

            drop(lock);
        }
    }

    /// Fetch total available chunks in [`FrozenFile`] from fs
    ///
    /// ## Working
    ///
    /// This call performs a syscall to fetch current length of [`FrozenFile`] from fs, as the current length of the
    /// file is not cached anywhere in the pipeline to avoid TOCTAU race conditions
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fpipe::{FrozenPipe, FPCfg};
    /// use frozen_core::bpool::BPBackend;
    /// use std::time::Duration;
    ///
    /// const MODULE_ID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_pipe_write");
    ///
    /// let cfg = FPCfg {
    ///     chunk_size: 0x20,
    ///     initial_chunk_amount: 2,
    ///     backend: BPBackend::Dynamic,
    ///     flush_duration: Duration::from_micros(0x3A),
    /// };
    ///
    /// let pipe = FrozenPipe::<MODULE_ID>::new(path, cfg).unwrap();
    ///
    /// let total_chunks = pipe.total_chunks().unwrap();
    /// assert_eq!(total_chunks, 2);
    /// ```
    #[inline]
    pub fn total_chunks(&self) -> FrozenRes<usize> {
        self.core.file.total_chunks()
    }

    #[inline(always)]
    fn read_2x(&self, index: usize) -> FrozenRes<Vec<u8>> {
        let chunk = self.core.cfg.chunk_size;

        let mut buf = vec![0u8; chunk * 2];
        let base = buf.as_mut_ptr();

        let ptrs = [base, unsafe { base.add(chunk) }];
        self.core.file.preadv(&ptrs, index)?;

        Ok(buf)
    }

    #[inline(always)]
    fn read_4x(&self, index: usize) -> FrozenRes<Vec<u8>> {
        let chunk = self.core.cfg.chunk_size;

        let mut buf = vec![0u8; chunk * 4];
        let base = buf.as_mut_ptr();

        let ptrs = [
            base,
            unsafe { base.add(chunk) },
            unsafe { base.add(chunk * 2) },
            unsafe { base.add(chunk * 3) },
        ];
        self.core.file.preadv(&ptrs, index)?;

        Ok(buf)
    }

    #[inline(always)]
    fn read_multi(&self, index: usize, count: usize) -> FrozenRes<Vec<u8>> {
        let chunk = self.core.cfg.chunk_size;

        let mut buf = vec![0u8; chunk * count];
        let base = buf.as_mut_ptr();

        let mut ptrs = Vec::with_capacity(count);
        for i in 0..count {
            ptrs.push(unsafe { base.add(i * chunk) });
        }

        self.core.file.preadv(&ptrs, index)?;
        Ok(buf)
    }

    fn internal_wait(&self, epoch: u64) -> FrozenRes<()> {
        if hints::unlikely(self.core.epoch.load(atomic::Ordering::Acquire) > epoch) {
            return Ok(());
        }

        if let Some(sync_err) = self.core.get_sync_error() {
            return Err(sync_err);
        }

        let mut guard = match self.core.durable_lock.lock() {
            Ok(g) => g,
            Err(e) => return new_err(err::LPN, e),
        };

        loop {
            if let Some(sync_err) = self.core.get_sync_error() {
                return Err(sync_err);
            }

            if self.core.epoch.load(atomic::Ordering::Acquire) > epoch {
                return Ok(());
            }

            guard = match self.core.durable_cv.wait(guard) {
                Ok(g) => g,
                Err(e) => return new_err(err::LPN, e),
            };
        }
    }
}

impl<const MODULE_ID: u8> Drop for FrozenPipe<MODULE_ID> {
    fn drop(&mut self) {
        self.core.closed.store(true, atomic::Ordering::Release);
        self.core.cv.notify_one(); // notify flusher tx to shut

        if let Some(handle) = self.tx.take() {
            let _ = handle.join();
        }

        // we must acquire an exclusive lock, to prevent dropping while sync, growing or any io ops
        let _io_lock = self.core.acquire_exclusive_io_lock();

        // free up the boxed error (if any)
        let ptr = self.core.error.swap(std::ptr::null_mut(), atomic::Ordering::AcqRel);
        if !ptr.is_null() {
            unsafe {
                drop(Box::from_raw(ptr));
            }
        }
    }
}

#[derive(Debug)]
struct Core {
    cfg: FPCfg,
    cv: sync::Condvar,
    pool: bpool::BufPool,
    lock: sync::Mutex<()>,
    file: ffile::FrozenFile,
    epoch: atomic::AtomicU64,
    io_lock: sync::RwLock<()>,
    durable_cv: sync::Condvar,
    closed: atomic::AtomicBool,
    durable_lock: sync::Mutex<()>,
    mpscq: mpscq::MPSCQueue<WriteReq>,
    error: atomic::AtomicPtr<FrozenErr>,
}

impl Core {
    fn new(file: ffile::FrozenFile, pool: bpool::BufPool, cfg: FPCfg) -> FrozenRes<sync::Arc<Self>> {
        Ok(sync::Arc::new(Self {
            cfg,
            file,
            pool,
            cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            io_lock: sync::RwLock::new(()),
            epoch: atomic::AtomicU64::new(0),
            durable_cv: sync::Condvar::new(),
            mpscq: mpscq::MPSCQueue::default(),
            durable_lock: sync::Mutex::new(()),
            closed: atomic::AtomicBool::new(false),
            error: atomic::AtomicPtr::new(std::ptr::null_mut()),
        }))
    }

    #[inline]
    fn acquire_io_lock(&self) -> FrozenRes<sync::RwLockReadGuard<'_, ()>> {
        self.io_lock.read().map_err(|e| new_err_raw(err::LPN, e))
    }

    #[inline]
    fn acquire_exclusive_io_lock(&self) -> FrozenRes<sync::RwLockWriteGuard<'_, ()>> {
        self.io_lock.write().map_err(|e| new_err_raw(err::LPN, e))
    }

    #[inline]
    fn get_sync_error(&self) -> Option<FrozenErr> {
        let ptr = self.error.load(atomic::Ordering::Acquire);
        if hints::likely(ptr.is_null()) {
            return None;
        }

        Some(unsafe { (*ptr).clone() })
    }

    #[inline]
    fn set_sync_error(&self, err: FrozenErr) {
        let boxed = Box::into_raw(Box::new(err));
        let old = self.error.swap(boxed, atomic::Ordering::AcqRel);

        // NOTE: we must free the old error, if any, to avoid mem leaks
        if !old.is_null() {
            unsafe {
                drop(Box::from_raw(old));
            }
        }
    }

    #[inline]
    fn clear_sync_error(&self) {
        let old = self.error.swap(std::ptr::null_mut(), atomic::Ordering::AcqRel);
        if hints::unlikely(!old.is_null()) {
            unsafe {
                drop(Box::from_raw(old));
            }
        }
    }

    #[inline]
    fn incr_epoch(&self) {
        self.epoch.fetch_add(1, atomic::Ordering::Release);
    }

    fn write_batch(&self, batch: Vec<WriteReq>) -> FrozenRes<(usize, usize)> {
        let mut max_index = 0usize;
        let mut min_index = usize::MAX;

        for req in &batch {
            let slots = req.alloc.slots();
            match req.chunks {
                1 => {
                    self.file.pwrite(slots[0], req.index)?;
                }
                _ => {
                    self.file.pwritev(slots, req.index)?;
                }
            }

            min_index = min_index.min(req.index);
            max_index = max_index.max(req.index + req.chunks);
        }

        Ok((min_index, max_index))
    }

    fn spawn_tx(core: sync::Arc<Self>) -> FrozenRes<thread::JoinHandle<()>> {
        match thread::Builder::new()
            .name("fpipe-flush-tx".into())
            .spawn(move || Self::flush_tx(core))
        {
            Ok(tx) => Ok(tx),
            Err(error) => new_err(err::FXE, error),
        }
    }

    fn flush_tx(core: sync::Arc<Self>) {
        // init phase (acquiring locks)
        let mut guard = match core.lock.lock() {
            Ok(g) => g,
            Err(error) => {
                core.set_sync_error(new_err_raw(err::FXE, error));
                return;
            }
        };

        // sync loop w/ non-busy waiting
        loop {
            guard = match core.cv.wait_timeout(guard, core.cfg.flush_duration) {
                Ok((g, _)) => g,
                Err(e) => {
                    core.set_sync_error(new_err_raw(err::TXE, e));
                    return;
                }
            };

            // INFO: we must drop the guard before syscall, as its a blocking operation and holding
            // the mutex while the syscall takes place is not a good idea, while we drop the mutex
            // and acqurie it again, in-between other process could acquire it and use it
            drop(guard);

            // NOTE: we must read values of close brodcast before acquire exclusive lock,
            // if done otherwise, we impose serious deadlock sort of situation for the the flusher tx

            let req_batch = core.mpscq.drain();
            let closing = core.closed.load(atomic::Ordering::Acquire);

            if req_batch.is_empty() {
                if closing {
                    return;
                }

                guard = match core.lock.lock() {
                    Ok(g) => g,
                    Err(e) => {
                        core.set_sync_error(new_err_raw(err::LPN, e));
                        return;
                    }
                };

                continue;
            }

            // INFO: we must acquire an exclusive IO lock for sync, hence no write/read ops are allowed
            // while sync is in progress

            let io_lock = match core.acquire_exclusive_io_lock() {
                Ok(lock) => lock,
                Err(err) => {
                    core.set_sync_error(err);
                    return;
                }
            };

            // QUESTION: If either of `write_batch`, `file.sync_range` or `file.sync` fails, the req_batch is dropped,
            // as its already drained from the MPSCQ, should we re-insert it so we could retry the same ops in the
            // next flush_tx cycle??

            let (_min, _max) = match core.write_batch(req_batch) {
                Ok(res) => res,
                Err(err) => {
                    core.set_sync_error(err);
                    drop(io_lock);

                    guard = match core.lock.lock() {
                        Ok(g) => g,
                        Err(e) => {
                            core.set_sync_error(new_err_raw(err::LPN, e));
                            return;
                        }
                    };

                    continue;
                }
            };

            // NOTE: On linux, we can initiate writeback (best-effort only) for a given range
            #[cfg(target_os = "linux")]
            if let Err(err) = core.file.sync_range(_min, _max - _min) {
                core.set_sync_error(err);
            }

            // NOTE:
            //
            // - if sync fails, we update the Core::error w/ the received error object
            // - we clear it up when another sync call succeeds
            // - this is valid, as the underlying sync flushes entire mmaped region, hence
            //   even if the last call failed, and the new one succeeded, we do get the durability
            //   guarenty for the old data as well

            match core.file.sync() {
                Err(err) => core.set_sync_error(err),
                Ok(()) => {
                    core.incr_epoch();
                    let _g = match core.durable_lock.lock() {
                        Ok(g) => g,
                        Err(e) => {
                            core.set_sync_error(new_err_raw(err::LPN, e));
                            return;
                        }
                    };

                    core.durable_cv.notify_all();
                    core.clear_sync_error();
                }
            }

            drop(io_lock);
            guard = match core.lock.lock() {
                Ok(g) => g,
                Err(e) => {
                    core.set_sync_error(new_err_raw(err::LPN, e));
                    return;
                }
            };
        }
    }
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

#[derive(Debug)]
struct WriteReq {
    index: usize,
    chunks: usize,
    alloc: bpool::Allocation,
}

impl WriteReq {
    fn new(index: usize, chunks: usize, alloc: bpool::Allocation) -> Self {
        Self { alloc, index, chunks }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Barrier};
    use std::thread;
    use std::time::{Duration, Instant};

    const MID: u8 = 0;
    const INIT: usize = 4;
    const CHUNK: usize = 0x10;

    // NOTE: we keep this small on purpose, so we won't have to wait at all in tests
    const FLUSH_DURATION: time::Duration = time::Duration::from_micros(10);

    fn new_env() -> (tempfile::TempDir, FrozenPipe<MID>) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tmp_pipe");

        let pipe = FrozenPipe::<MID>::new(
            path,
            FPCfg {
                chunk_size: CHUNK,
                initial_chunk_amount: INIT,
                flush_duration: FLUSH_DURATION,
                backend: bpool::BPBackend::Dynamic,
            },
        )
        .unwrap();

        (dir, pipe)
    }

    mod lifecycle {
        use super::*;

        #[test]
        fn ok_new() {
            let (_dir, pipe) = new_env();
            assert_eq!(pipe.core.epoch.load(atomic::Ordering::Acquire), 0);
        }

        #[test]
        fn ok_drop() {
            let (_dir, pipe) = new_env();
            drop(pipe);
        }
    }

    mod fp_write {
        use super::*;

        #[test]
        fn ok_write_and_wait() {
            let (_dir, pipe) = new_env();

            let buf = vec![0xAB; CHUNK];
            let epoch = pipe.write(&buf, 0).unwrap();
            pipe.wait_for_durability(epoch).unwrap();
        }

        #[test]
        fn ok_write_multiple_chunks() {
            let (_dir, pipe) = new_env();

            let buf = vec![0xAA; CHUNK * 4];
            let epoch = pipe.write(&buf, 0).unwrap();
            pipe.wait_for_durability(epoch).unwrap();
        }

        #[test]
        fn ok_force_durability() {
            let (_dir, pipe) = new_env();

            let buf = vec![1u8; CHUNK];
            let epoch = pipe.write(&buf, 0).unwrap();
            pipe.force_durability(epoch).unwrap();
        }

        #[test]
        fn ok_write_epoch_monotonic() {
            let (_dir, pipe) = new_env();
            let buf = vec![1u8; CHUNK];

            let e1 = pipe.write(&buf, 0).unwrap();
            pipe.wait_for_durability(e1).unwrap();

            let e2 = pipe.write(&buf, 1).unwrap();
            pipe.wait_for_durability(e2).unwrap();

            assert!(e2 >= e1);
        }

        #[test]
        fn ok_write_large() {
            let (_dir, pipe) = new_env();
            let buf = vec![0xAB; CHUNK * 0x80];

            let epoch = pipe.write(&buf, 0).unwrap();
            pipe.wait_for_durability(epoch).unwrap();
        }

        #[test]
        fn ok_write_large_batch() {
            let (_dir, pipe) = new_env();

            for i in 0..0x10 {
                let buf = vec![i as u8; CHUNK];
                let epoch = pipe.write(&buf, i).unwrap();
                pipe.wait_for_durability(epoch).unwrap();
            }
        }

        #[test]
        fn ok_write_is_blocked_at_pool_exhaustion_for_prealloc_backend() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("tmp_pipe");

            let cfg = FPCfg {
                chunk_size: CHUNK,
                initial_chunk_amount: INIT,
                backend: bpool::BPBackend::Prealloc { capacity: 1 },
                flush_duration: FLUSH_DURATION,
            };
            let pipe = Arc::new(FrozenPipe::<MID>::new(path, cfg).unwrap());

            let p2 = pipe.clone();
            let t = thread::spawn(move || {
                let buf = vec![1u8; CHUNK];
                let epoch = p2.write(&buf, 0).unwrap();
                p2.wait_for_durability(epoch).unwrap();
            });

            thread::sleep(Duration::from_millis(0x0A));

            let buf = vec![2u8; CHUNK];
            let epoch = pipe.write(&buf, 1).unwrap();
            pipe.wait_for_durability(epoch).unwrap();

            t.join().unwrap();
        }
    }

    mod fp_read {
        use super::*;

        #[test]
        fn ok_read_single_after_write() {
            let (_dir, pipe) = new_env();

            let buf = vec![0xAB; CHUNK];
            let epoch = pipe.write(&buf, 0).unwrap();
            pipe.wait_for_durability(epoch).unwrap();

            let read = pipe.read_single(0).unwrap();
            assert_eq!(read, buf);
        }

        #[test]
        fn ok_read_2x() {
            let (_dir, pipe) = new_env();

            let buf = vec![0xAA; CHUNK * 2];
            let epoch = pipe.write(&buf, 0).unwrap();
            pipe.wait_for_durability(epoch).unwrap();

            let read = pipe.read(0, 2).unwrap();
            assert_eq!(read, buf);
        }

        #[test]
        fn ok_read_4x() {
            let (_dir, pipe) = new_env();

            let buf = vec![0xBB; CHUNK * 4];
            let epoch = pipe.write(&buf, 0).unwrap();
            pipe.wait_for_durability(epoch).unwrap();

            let read = pipe.read(0, 4).unwrap();
            assert_eq!(read, buf);
        }

        #[test]
        fn ok_read_multi_generic() {
            let (_dir, pipe) = new_env();

            let buf = vec![0xCC; CHUNK * 6];
            let epoch = pipe.write(&buf, 0).unwrap();
            pipe.wait_for_durability(epoch).unwrap();

            let read = pipe.read(0, 6).unwrap();
            assert_eq!(read, buf);
        }

        #[test]
        fn ok_read_multiple_indices() {
            let (_dir, pipe) = new_env();

            for i in 0..2 {
                let buf = vec![i as u8; CHUNK];
                let epoch = pipe.write(&buf, i).unwrap();
                pipe.wait_for_durability(epoch).unwrap();
            }

            for i in 0..2 {
                let read = pipe.read_single(i).unwrap();
                assert_eq!(read, vec![i as u8; CHUNK]);
            }
        }

        #[test]
        fn ok_overwrite_same_index() {
            let (_dir, pipe) = new_env();

            let buf1 = vec![0xAA; CHUNK];
            let e1 = pipe.write(&buf1, 0).unwrap();
            pipe.wait_for_durability(e1).unwrap();

            let buf2 = vec![0xBB; CHUNK];
            let e2 = pipe.write(&buf2, 0).unwrap();
            pipe.wait_for_durability(e2).unwrap();

            let read = pipe.read_single(0).unwrap();
            assert_eq!(read, buf2);
        }

        #[test]
        fn ok_large_read_multi() {
            let (_dir, pipe) = new_env();

            let buf = vec![0x7A; CHUNK * 0x10];
            let epoch = pipe.write(&buf, 0).unwrap();
            pipe.wait_for_durability(epoch).unwrap();

            let read = pipe.read(0, 0x10).unwrap();
            assert_eq!(read, buf);
        }

        #[test]
        fn ok_read_concurrent() {
            const THREADS: usize = 2;

            let (_dir, pipe) = new_env();
            let pipe = Arc::new(pipe);

            for i in 0..THREADS {
                let buf = vec![i as u8; CHUNK];
                let epoch = pipe.write(&buf, i).unwrap();
                pipe.wait_for_durability(epoch).unwrap();
            }

            let mut handles = Vec::new();

            for i in 0..THREADS {
                let pipe = pipe.clone();

                handles.push(thread::spawn(move || {
                    let read = pipe.read_single(i).unwrap();
                    assert_eq!(read, vec![i as u8; CHUNK]);
                }));
            }

            for h in handles {
                h.join().unwrap();
            }
        }

        #[test]
        fn ok_concurrent_read_write() {
            let (_dir, pipe) = new_env();
            let pipe = Arc::new(pipe);

            let writer = {
                let pipe = pipe.clone();
                thread::spawn(move || {
                    for i in 0..4 {
                        let buf = vec![i as u8; CHUNK];
                        let epoch = pipe.write(&buf, i).unwrap();
                        pipe.wait_for_durability(epoch).unwrap();
                    }
                })
            };

            let reader = {
                let pipe = pipe.clone();
                thread::spawn(move || {
                    for _ in 0..4 {
                        let _ = pipe.read_single(0);
                    }
                })
            };

            writer.join().unwrap();
            reader.join().unwrap();
        }

        #[test]
        fn ok_read_after_grow() {
            let (_dir, pipe) = new_env();

            pipe.grow(8).unwrap();

            let buf = vec![0x5A; CHUNK];
            let epoch = pipe.write(&buf, INIT).unwrap();
            pipe.wait_for_durability(epoch).unwrap();

            let read = pipe.read_single(INIT).unwrap();
            assert_eq!(read, buf);
        }
    }

    mod batching {
        use super::*;

        #[test]
        fn ok_multiple_writes_single_batch() {
            let (_dir, pipe) = new_env();

            let mut epochs = Vec::new();
            for i in 0..4 {
                let buf = vec![i as u8; CHUNK];
                epochs.push(pipe.write(&buf, i).unwrap());
            }

            for e in epochs {
                pipe.wait_for_durability(e).unwrap();
            }

            assert!(pipe.core.epoch.load(atomic::Ordering::Acquire) > 0);
        }
    }

    mod fp_grow {
        use super::*;

        #[test]
        fn ok_grow_file() {
            let (_dir, pipe) = new_env();
            let curr_len = pipe.core.file.length().unwrap();

            pipe.grow(0x10).unwrap();
            let new_len = pipe.core.file.length().unwrap();

            assert_eq!(new_len, curr_len + (0x10 * pipe.core.cfg.chunk_size));
        }

        #[test]
        fn ok_write_after_grow() {
            let (_dir, pipe) = new_env();
            pipe.grow(0x10).unwrap();

            let buf = vec![0xBB; CHUNK];
            let epoch = pipe.write(&buf, INIT).unwrap();
            pipe.wait_for_durability(epoch).unwrap();
        }

        #[test]
        fn ok_grow_while_writing() {
            let (_dir, pipe) = new_env();
            let pipe = Arc::new(pipe);
            let curr_len = pipe.core.file.length().unwrap();

            let p2 = pipe.clone();
            let writer = thread::spawn(move || {
                for i in 0..INIT {
                    let buf = vec![1u8; CHUNK];
                    let epoch = p2.write(&buf, i).unwrap();
                    p2.wait_for_durability(epoch).unwrap();
                }
            });

            thread::sleep(Duration::from_millis(10));

            pipe.grow(0x3A).unwrap();
            writer.join().unwrap();

            let new_len = pipe.core.file.length().unwrap();
            assert_eq!(new_len, curr_len + (0x3A * pipe.core.cfg.chunk_size));
        }
    }

    mod concurrency {
        use super::*;

        #[test]
        fn ok_multi_writer() {
            const THREADS: usize = 2;
            const ITERS: usize = 0x10;

            let (_dir, pipe) = new_env();
            let pipe = Arc::new(pipe);

            let mut handles = Vec::new();
            for t in 0..THREADS {
                let pipe = pipe.clone();

                handles.push(thread::spawn(move || {
                    for i in 0..ITERS {
                        let buf = vec![t as u8; CHUNK];
                        let epoch = pipe.write(&buf, i).unwrap();
                        pipe.wait_for_durability(epoch).unwrap();
                    }
                }));
            }

            for h in handles {
                h.join().unwrap();
            }
        }

        #[test]
        fn ok_barrier_start_parallel_writes() {
            const THREADS: usize = 2;

            let (_dir, pipe) = new_env();
            let pipe = Arc::new(pipe);
            let barrier = Arc::new(Barrier::new(THREADS));

            let mut handles = Vec::new();

            for i in 0..THREADS {
                let pipe = pipe.clone();
                let barrier = barrier.clone();

                handles.push(thread::spawn(move || {
                    barrier.wait();

                    let buf = vec![i as u8; CHUNK];
                    let epoch = pipe.write(&buf, i).unwrap();
                    pipe.wait_for_durability(epoch).unwrap();
                }));
            }

            for h in handles {
                h.join().unwrap();
            }
        }
    }

    mod durability_wait {
        use super::*;

        #[test]
        fn ok_wait_blocks_until_flush() {
            let (_dir, pipe) = new_env();

            let buf = vec![0x55; CHUNK];
            let epoch = pipe.write(&buf, 0).unwrap();

            let start = Instant::now();
            pipe.wait_for_durability(epoch).unwrap();

            assert!(start.elapsed() >= Duration::from_micros(1));
        }

        #[test]
        fn ok_force_durability_concurrent() {
            let (_dir, pipe) = new_env();
            let pipe = Arc::new(pipe);

            let mut handles = Vec::new();
            for i in 0..4 {
                let pipe = pipe.clone();

                handles.push(thread::spawn(move || {
                    let buf = vec![i as u8; CHUNK];
                    let epoch = pipe.write(&buf, i).unwrap();
                    pipe.force_durability(epoch).unwrap();
                }));
            }

            for h in handles {
                h.join().unwrap();
            }
        }
    }

    mod shutdown {
        use super::*;

        #[test]
        fn ok_drop_with_pending_writes() {
            let (_dir, pipe) = new_env();

            let buf = vec![0xAA; CHUNK];
            pipe.write(&buf, 0).unwrap();
            drop(pipe);
        }

        #[test]
        fn ok_drop_during_activity() {
            let (_dir, pipe) = new_env();
            let pipe = Arc::new(pipe);

            let p2 = pipe.clone();
            let handle = thread::spawn(move || {
                let buf = vec![1u8; CHUNK];
                let epoch = p2.write(&buf, 0).unwrap();
                p2.wait_for_durability(epoch).unwrap();
            });

            thread::sleep(Duration::from_millis(10));
            drop(pipe);

            handle.join().unwrap();
        }

        #[test]
        fn ok_drop_while_writer_waiting() {
            let (_dir, pipe) = new_env();
            let pipe = Arc::new(pipe);

            let p2 = pipe.clone();
            let handle = thread::spawn(move || {
                for i in 0..0x10 {
                    let buf = vec![1u8; CHUNK];
                    let epoch = p2.write(&buf, i).unwrap();
                    p2.wait_for_durability(epoch).unwrap();
                }
            });

            thread::sleep(Duration::from_millis(0x0A));
            drop(pipe);

            handle.join().unwrap();
        }
    }
}
