//! A low latency asynchronous write pipeline for buffer based storage
//!
//! ## Design
//!
//! By design, every write call is fire-and-forget, i.e. the call is immediately returned after
//! pushing the bytes to be written into the MPSC queue.
//!
//! The background thread pulls from MPSC queue and performs indivisual pwrite/v calls and a common
//! hard sync right after. This provides durability for all the writes submitted within the same
//! [`WritePipeCfg::flush_duration`] batching window.
//!
//! ## Benchmarks
//!
//! Observed measurements for latency (both single and multi threaded),
//!
//! | Metric | 1 Thread (µs) | 4 Threads (µs) |
//! |:-------|:--------------|:---------------|
//! | P50    |         0.091 |          0.275 |
//! | P90    |         0.092 |          0.458 |
//! | P99    |         0.825 |          0.917 |
//! | Mean   |         1.185 |          3.857 |
//!
//! Environment used for benching,
//!
//! * OS: NixOS (WSL2)
//! * Architecture: x86_64
//! * Memory: 8 GiB RAM (DDR4)
//! * Rust: rustc 1.86.0 w/ cargo 1.86.0
//! * Kernel: Linux 6.6.87.2-microsoft-standard-WSL2
//! * CPU: Intel® Core™ i5-10300H @ 2.50GHz (4C / 8T)
//!
//! ## Example
//!
//! ```
//! use frozen_core::{bufpool, ffile, utils, wpipe};
//! use std::{ptr, sync, time};
//!
//! const MODULE_ID: u8 = 0x00;
//! const BUFFER_SIZE: utils::BufferSize = utils::BufferSize::S128;
//!
//! let dir = tempfile::tempdir().expect("tempdir creation should succeed");
//! let path = dir.path().join("wpipe_example");
//!
//! let file_cfg = ffile::FrozenFileCfg {
//!     path,
//!     module_id: MODULE_ID,
//!     initial_available_buffers: 0x400,
//!     buffer_size: BUFFER_SIZE as usize,
//! };
//! let file = sync::Arc::new(
//!     ffile::FrozenFile::new(file_cfg)
//!         .expect("file creation should succeed"),
//! );
//!
//! let pool_cfg = bufpool::BufPoolCfg {
//!     buffer_size: utils::BufferSize::S128,
//!     max_memory: 0x400 * BUFFER_SIZE as usize,
//! };
//! let pool = bufpool::BufPool::new(pool_cfg);
//!
//! let pipe_cfg = wpipe::WritePipeCfg {
//!     module_id: MODULE_ID,
//!     flush_duration: time::Duration::from_millis(1),
//! };
//! let pipe = wpipe::WritePipe::new(pipe_cfg, file)
//!     .expect("pipe creation should succeed");
//!
//! let payload = [0xAAu8; BUFFER_SIZE as usize];
//!
//! let mut latest_ticket = None;
//! for slot_index in 0..3 {
//!     let allocation = pool.allocate(1);
//!
//!     unsafe {
//!         ptr::copy_nonoverlapping(
//!             payload.as_ptr(),
//!             allocation.first(),
//!             payload.len(),
//!         );
//!     }
//!
//!     let ticket = pipe
//!         .write(wpipe::WriteRequest {
//!             allocation,
//!             slot_index,
//!         })
//!         .expect("write should succeed");
//!
//!     latest_ticket = Some(ticket);
//! }
//!
//! let durable_epoch = futures::executor::block_on(
//!     latest_ticket.expect("ticket should exist"),
//! )
//! .expect("writes should become durable");
//!
//! assert!(durable_epoch >= 3);
//! ```

use crate::{ack, bufpool, error::FrozenResult, ffile, mpscq};
use std::{
    sync::{self, atomic},
    thread, time,
};

/// All the available configurations for [`WritePipe`]
///
/// ## Example
///
/// ```
/// use frozen_core::wpipe::WritePipeCfg;
///
/// let cfg = WritePipeCfg {
///     module_id: 2,
///     flush_duration: std::time::Duration::from_millis(0x0A),
/// };
///
/// assert_ne!(cfg.module_id, 0);
/// assert_ne!(cfg.flush_duration.as_millis(), 0);
/// ```
#[derive(Debug, Clone)]
pub struct WritePipeCfg {
    /// Identifier used for error propagation by [`frozen_core::error::FrozenError`]
    pub module_id: u8,

    /// Time interval used by the background thread to perform hard sync for all the write
    /// operations submitted in the last durability window
    pub flush_duration: time::Duration,
}

/// A low latency asynchronous write pipeline for buffer based storage
///
/// ## Design
///
/// By design, every write call is fire-and-forget, i.e. the call is immediately returned after
/// pushing the bytes to be written into the MPSC queue.
///
/// The background thread pulls from MPSC queue and performs indivisual pwrite/v calls and a common
/// hard sync right after. This provides durability for all the writes submitted within the same
/// [`WritePipeCfg::flush_duration`] batching window.
///
/// ## Example
///
/// ```
/// use frozen_core::{bufpool, ffile, utils, wpipe};
/// use std::{ptr, sync, time};
///
/// const MODULE_ID: u8 = 0x00;
/// const BUFFER_SIZE: utils::BufferSize = utils::BufferSize::S128;
///
/// let dir = tempfile::tempdir().expect("tempdir creation should succeed");
/// let path = dir.path().join("wpipe_example");
///
/// let file_cfg = ffile::FrozenFileCfg {
///     path,
///     module_id: MODULE_ID,
///     initial_available_buffers: 0x400,
///     buffer_size: BUFFER_SIZE as usize,
/// };
/// let file = sync::Arc::new(
///     ffile::FrozenFile::new(file_cfg)
///         .expect("file creation should succeed"),
/// );
///
/// let pool_cfg = bufpool::BufPoolCfg {
///     buffer_size: utils::BufferSize::S128,
///     max_memory: 0x400 * BUFFER_SIZE as usize,
/// };
/// let pool = bufpool::BufPool::new(pool_cfg);
///
/// let pipe_cfg = wpipe::WritePipeCfg {
///     module_id: MODULE_ID,
///     flush_duration: time::Duration::from_millis(1),
/// };
/// let pipe = wpipe::WritePipe::new(pipe_cfg, file)
///     .expect("pipe creation should succeed");
///
/// let payload = [0xAAu8; BUFFER_SIZE as usize];
///
/// let mut latest_ticket = None;
/// for slot_index in 0..3 {
///     let allocation = pool.allocate(1);
///
///     unsafe {
///         ptr::copy_nonoverlapping(
///             payload.as_ptr(),
///             allocation.first(),
///             payload.len(),
///         );
///     }
///
///     let ticket = pipe
///         .write(wpipe::WriteRequest {
///             allocation,
///             slot_index,
///         })
///         .expect("write should succeed");
///
///     latest_ticket = Some(ticket);
/// }
///
/// let durable_epoch = futures::executor::block_on(
///     latest_ticket.expect("ticket should exist"),
/// )
/// .expect("writes should become durable");
///
/// assert!(durable_epoch >= 3);
/// ```
#[derive(Debug)]
pub struct WritePipe {
    core: sync::Arc<Core>,
    flush_tx_handle: Option<thread::JoinHandle<()>>,
}

unsafe impl Send for WritePipe {}
unsafe impl Sync for WritePipe {}

impl WritePipe {
    /// Create a new instance of [`WritePipe`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{bufpool, ffile, utils, wpipe};
    /// use std::{ptr, sync, time};
    ///
    /// const MODULE_ID: u8 = 0x00;
    /// const BUFFER_SIZE: utils::BufferSize = utils::BufferSize::S128;
    ///
    /// let dir = tempfile::tempdir().expect("tempdir creation should succeed");
    /// let path = dir.path().join("wpipe_example");
    ///
    /// let file_cfg = ffile::FrozenFileCfg {
    ///     path,
    ///     module_id: MODULE_ID,
    ///     initial_available_buffers: 0x400,
    ///     buffer_size: BUFFER_SIZE as usize,
    /// };
    /// let file = sync::Arc::new(
    ///     ffile::FrozenFile::new(file_cfg)
    ///         .expect("file creation should succeed"),
    /// );
    ///
    /// let pool_cfg = bufpool::BufPoolCfg {
    ///     buffer_size: utils::BufferSize::S128,
    ///     max_memory: 0x400 * BUFFER_SIZE as usize,
    /// };
    /// let pool = bufpool::BufPool::new(pool_cfg);
    ///
    /// let pipe_cfg = wpipe::WritePipeCfg {
    ///     module_id: MODULE_ID,
    ///     flush_duration: time::Duration::from_millis(1),
    /// };
    /// let pipe = wpipe::WritePipe::new(pipe_cfg, file)
    ///     .expect("pipe creation should succeed");
    ///
    /// let payload = vec![0x0A; BUFFER_SIZE as usize];
    /// let allocation = pool.allocate(1);
    ///
    /// unsafe {ptr::copy_nonoverlapping(
    ///     payload.as_ptr(),
    ///     allocation.first(),
    ///     payload.len()
    /// )};
    ///
    /// let ticket = pipe.write(wpipe::WriteRequest {allocation, slot_index: 0});
    ///
    /// assert!(
    ///     futures::executor::block_on(ticket.expect("ticket should exist"))
    ///     .is_ok()
    /// );
    /// ```
    #[inline]
    pub fn new(cfg: WritePipeCfg, file: sync::Arc<ffile::FrozenFile>) -> FrozenResult<Self> {
        let core = sync::Arc::new(Core::new(file));
        let cloned_core = core.clone();
        let flush_tx_handle = match thread::Builder::new()
            .name(format!("mod{}_wpipe_flush_tx", cfg.module_id))
            .spawn(move || bg_flush_thread(cloned_core, cfg.flush_duration))
        {
            Ok(handle) => Some(handle),
            Err(observed_error) => {
                return Err(err::new_error(cfg.module_id, err::FXE, observed_error));
            }
        };

        Ok(Self { core: core, flush_tx_handle })
    }

    /// Push a write into [`WritePipe`]
    ///
    /// Every write call is fire-and-forget for the caller by default, unless the caller choose to
    /// wait for durability using the manual `await` on [`WriteTicket`].
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{bufpool, ffile, utils, wpipe};
    /// use std::{ptr, sync, time};
    ///
    /// const MODULE_ID: u8 = 0x00;
    /// const BUFFER_SIZE: utils::BufferSize = utils::BufferSize::S128;
    ///
    /// let dir = tempfile::tempdir().expect("tempdir creation should succeed");
    /// let path = dir.path().join("wpipe_example");
    ///
    /// let file_cfg = ffile::FrozenFileCfg {
    ///     path,
    ///     module_id: MODULE_ID,
    ///     initial_available_buffers: 0x400,
    ///     buffer_size: BUFFER_SIZE as usize,
    /// };
    /// let file = sync::Arc::new(
    ///     ffile::FrozenFile::new(file_cfg)
    ///         .expect("file creation should succeed"),
    /// );
    ///
    /// let pool_cfg = bufpool::BufPoolCfg {
    ///     buffer_size: utils::BufferSize::S128,
    ///     max_memory: 0x400 * BUFFER_SIZE as usize,
    /// };
    /// let pool = bufpool::BufPool::new(pool_cfg);
    ///
    /// let pipe_cfg = wpipe::WritePipeCfg {
    ///     module_id: MODULE_ID,
    ///     flush_duration: time::Duration::from_millis(1),
    /// };
    /// let pipe = wpipe::WritePipe::new(pipe_cfg, file)
    ///     .expect("pipe creation should succeed");
    ///
    /// let payload = vec![0x0A; BUFFER_SIZE as usize];
    /// let allocation = pool.allocate(1);
    ///
    /// unsafe {ptr::copy_nonoverlapping(
    ///     payload.as_ptr(),
    ///     allocation.first(),
    ///     payload.len()
    /// )};
    ///
    /// let ticket = pipe.write(wpipe::WriteRequest {allocation, slot_index: 0});
    ///
    /// assert!(
    ///     futures::executor::block_on(ticket.expect("ticket should exist"))
    ///     .is_ok()
    /// );
    /// ```
    #[inline]
    pub fn write(&self, request: WriteRequest) -> FrozenResult<ack::AckTicket> {
        let _io_lock = self.core.acquire_shared_io_lock();
        if let Some(frozen_error) = self.core.completion.get_err() {
            return Err(frozen_error);
        }

        let epoch = self.core.completion.increment_current_epoch();
        let internal_req = WriteRequestInternal { request, epoch };
        self.core.queue.push(internal_req);

        Ok(ack::AckTicket::new(epoch, self.core.completion.clone()))
    }
}

impl Drop for WritePipe {
    fn drop(&mut self) {
        self.core.closed.store(true, atomic::Ordering::Release);
        self.core.flush_cv.notify_one();

        if let Some(handle) = self.flush_tx_handle.take() {
            let _ = handle.join();
        }
    }
}

/// A write operation submitted to [`WritePipe`]
///
/// The request contains the buffers to persist along with the destination slot index in the
/// underlying [`FrozenFile`].
///
/// ## Example
///
/// ```
/// use frozen_core::{bufpool, utils, wpipe};
/// use std::ptr;
///
/// const BUFFER_SIZE: utils::BufferSize = utils::BufferSize::S128;
///
/// let pool_cfg = bufpool::BufPoolCfg {
///     buffer_size: utils::BufferSize::S128,
///     max_memory: 0x400 * BUFFER_SIZE as usize,
/// };
/// let pool = bufpool::BufPool::new(pool_cfg);
///
/// let payload = vec![0x0A; BUFFER_SIZE as usize];
/// let allocation = pool.allocate(1);
///
/// unsafe {ptr::copy_nonoverlapping(
///     payload.as_ptr(),
///     allocation.first(),
///     payload.len()
/// )};
///
/// let request = wpipe::WriteRequest {allocation, slot_index: 0};
/// assert!(request.slot_index >= 0);
/// ```
#[derive(Debug)]
pub struct WriteRequest {
    /// Buffer allocation containing the pages to be written allocated using [`bufpool::BufPool`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{bufpool, utils, wpipe};
    /// use std::ptr;
    ///
    /// const BUFFER_SIZE: utils::BufferSize = utils::BufferSize::S128;
    ///
    /// let pool_cfg = bufpool::BufPoolCfg {
    ///     buffer_size: utils::BufferSize::S128,
    ///     max_memory: 0x400 * BUFFER_SIZE as usize,
    /// };
    /// let pool = bufpool::BufPool::new(pool_cfg);
    ///
    /// let payload = vec![0x0A; BUFFER_SIZE as usize];
    /// let allocation = pool.allocate(1);
    ///
    /// unsafe {ptr::copy_nonoverlapping(
    ///     payload.as_ptr(),
    ///     allocation.first(),
    ///     payload.len()
    /// )};
    ///
    /// let request = wpipe::WriteRequest {allocation, slot_index: 0};
    /// assert!(!request.allocation.first().is_null());
    /// ```
    pub allocation: bufpool::BufPoolAllocation,

    /// Destination slot index where the pages of the allocation will be written from
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{bufpool, utils, wpipe};
    /// use std::ptr;
    ///
    /// const BUFFER_SIZE: utils::BufferSize = utils::BufferSize::S128;
    ///
    /// let pool_cfg = bufpool::BufPoolCfg {
    ///     buffer_size: utils::BufferSize::S128,
    ///     max_memory: 0x400 * BUFFER_SIZE as usize,
    /// };
    /// let pool = bufpool::BufPool::new(pool_cfg);
    ///
    /// let payload = vec![0x0A; BUFFER_SIZE as usize];
    /// let allocation = pool.allocate(1);
    ///
    /// unsafe {ptr::copy_nonoverlapping(
    ///     payload.as_ptr(),
    ///     allocation.first(),
    ///     payload.len()
    /// )};
    ///
    /// let request = wpipe::WriteRequest {allocation, slot_index: 0};
    /// assert!(request.slot_index >= 0);
    /// ```
    pub slot_index: usize,
}

/// ## Why we ignore [`std::sync::PoisonError`]?
///
/// The mutex used for lock, is solely used as a parking primitive for [`Condvar`] and does not
/// protect any mutable state. All the pool invariants and accounting are maintained via atomics
/// and are completely seperated from the mutex.
///
/// A poisoned mutex only indicates that another tx panicked while holding the lock, and indicates
/// an inconsistent state of the protected value. Since no state can be left partially modified
/// under this lock, there is no possible consistency risk to recover from and propagating the
/// poison error would only introduce unnecessary failures into the allocation path.
///
/// Therefore, as best effort, we consume the [`std::sync::PoisonError`] and continue operating
/// with the recovered guard.
fn bg_flush_thread(core: sync::Arc<Core>, flush_duration: time::Duration) {
    let mut guard = core.flush_guard.lock().unwrap_or_else(|e| e.into_inner());
    loop {
        (guard, _) =
            core.flush_cv.wait_timeout(guard, flush_duration).unwrap_or_else(|e| e.into_inner());

        // NOTE: we must read values of close brodcast before acquire exclusive lock, if done
        // otherwise, we impose serious deadlock sort of situation for the the flusher tx

        let queued_ops = core.queue.drain();
        let closed = core.closed.load(atomic::Ordering::Acquire);

        if queued_ops.is_empty() {
            if closed {
                return;
            }

            continue;
        }

        // INFO: we must acquire an exclusive IO lock for sync, hence no write/read ops are allowed
        // while sync is in progress
        let _io_lock = core.acquire_exclusive_io_lock();

        let (_min_index, _max_index, max_epoch) = match core.write_queued_ops(queued_ops) {
            Ok(res) => res,
            Err(new_error) => {
                core.completion.set_err(new_error);
                core.completion.notify_all_listeners();
                drop(_io_lock);

                continue;
            }
        };

        // NOTE: On linux, we can initiate writeback (best-effort only) for a given range
        #[cfg(target_os = "linux")]
        if let Err(new_error) = core.file.sync_range(_min_index, _max_index - _min_index) {
            core.completion.set_err(new_error);
            core.completion.notify_all_listeners();
            drop(_io_lock);

            continue;
        }

        // NOTE: If the sync fails, we update the Core::error w/ the received error object. We
        // clear it up when another call succeeds.
        //
        // This is valid as the underlying sync flushes entire batch all at once, hence even if the
        // last call failed, and the new one succeeded, we do get the durability guarantee for the
        // old data as well.

        if let Err(new_error) = core.file.sync() {
            core.completion.set_err(new_error);
            drop(_io_lock);

            continue;
        } else {
            core.completion.mark_epoch_as_durable(max_epoch);
            core.completion.del_err();
        }

        core.completion.notify_all_listeners();
    }
}

#[derive(Debug)]
struct Core {
    completion: sync::Arc<ack::Completion>,
    closed: atomic::AtomicBool,
    file: sync::Arc<ffile::FrozenFile>,
    flush_cv: sync::Condvar,
    flush_guard: sync::Mutex<()>,
    io_lock: sync::RwLock<()>,
    queue: mpscq::MPSCQueue<WriteRequestInternal>,
}

impl Core {
    fn new(file: sync::Arc<ffile::FrozenFile>) -> Self {
        Self {
            file,
            completion: sync::Arc::new(ack::Completion::default()),
            closed: atomic::AtomicBool::new(false),
            flush_cv: sync::Condvar::new(),
            flush_guard: sync::Mutex::new(()),
            io_lock: sync::RwLock::new(()),
            queue: mpscq::MPSCQueue::default(),
        }
    }

    #[inline]
    fn acquire_shared_io_lock(&self) -> sync::RwLockReadGuard<'_, ()> {
        // NOTE: See [`bg_flush_thread`] implementation for rationale behind poison recovery
        self.io_lock.read().unwrap_or_else(|e| e.into_inner())
    }

    #[inline]
    fn acquire_exclusive_io_lock(&self) -> sync::RwLockWriteGuard<'_, ()> {
        // NOTE: See [`bg_flush_thread`] implementation for rationale behind poison recovery
        self.io_lock.write().unwrap_or_else(|e| e.into_inner())
    }

    #[inline(always)]
    fn write_queued_ops(
        &self,
        queued_ops: Vec<WriteRequestInternal>,
    ) -> FrozenResult<(usize, usize, u64)> {
        let mut max_epoch = 0;
        let mut max_index = 0;
        let mut min_index = usize::MAX;

        for op in queued_ops {
            let ops_len = op.request.allocation.length();
            match ops_len {
                1 => {
                    self.file.pwrite(op.request.allocation.first(), op.request.slot_index)?;
                }
                _ => {
                    let bufs: Vec<bufpool::BufferPointer> = op.request.allocation.iter().collect();
                    self.file.pwritev(&bufs, op.request.slot_index)?;
                }
            }

            max_epoch = max_epoch.max(op.epoch);
            min_index = min_index.min(op.request.slot_index);
            max_index = max_index.max(op.request.slot_index + ops_len);
        }

        Ok((min_index, max_index, max_epoch))
    }
}

#[derive(Debug)]
struct WriteRequestInternal {
    epoch: u64,
    request: WriteRequest,
}

mod err {
    use crate::error::{ErrCode, FrozenError};

    /// Domain ID for [`wpipe`] module is `0x02` used while propagating errors
    const DOMAIN_ID: u8 = 0x02;

    #[inline]
    pub fn new_error<E: std::fmt::Display>(
        module_id: u8,
        code: ErrCode,
        observed_error: E,
    ) -> FrozenError {
        FrozenError::new_raw(module_id, DOMAIN_ID, code, observed_error)
    }

    pub const FXE: ErrCode = ErrCode::new(0x10, "unable to spawn background flush thread");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::BufferSize;

    const MODULE_ID: u8 = 0x00;
    const BUFFER_SIZE: BufferSize = BufferSize::S128;
    const INITIAL_BUFFER_AMOUT: usize = 0x200;
    const FLUSH_DURATION: time::Duration = time::Duration::from_millis(1);

    fn new_objects<P: AsRef<std::path::Path>>(
        path: P,
    ) -> (sync::Arc<ffile::FrozenFile>, bufpool::BufPool, WritePipe) {
        let file_cfg = ffile::FrozenFileCfg {
            module_id: MODULE_ID,
            path: path.as_ref().to_path_buf(),
            buffer_size: BUFFER_SIZE as usize,
            initial_available_buffers: INITIAL_BUFFER_AMOUT,
        };
        let file = sync::Arc::new(ffile::FrozenFile::new(file_cfg).unwrap());

        let pool_cfg = bufpool::BufPoolCfg {
            buffer_size: BUFFER_SIZE,
            max_memory: INITIAL_BUFFER_AMOUT * BUFFER_SIZE as usize,
        };
        let pool = bufpool::BufPool::new(pool_cfg);

        let pipe_cfg = WritePipeCfg { module_id: MODULE_ID, flush_duration: FLUSH_DURATION };
        let pipe = WritePipe::new(pipe_cfg, file.clone()).unwrap();

        (file, pool, pipe)
    }

    fn prep_write(
        buf_ptr: *const u8,
        n: usize,
        pool: &bufpool::BufPool,
    ) -> bufpool::BufPoolAllocation {
        let allocation = pool.allocate(n);
        for allocated_buf in allocation.iter() {
            unsafe { std::ptr::copy_nonoverlapping(buf_ptr, allocated_buf, BUFFER_SIZE as usize) };
        }

        allocation
    }

    fn compare_with_readback(
        buf: &[u8],
        read_index: usize,
        required: usize,
        pool: &bufpool::BufPool,
        file: &ffile::FrozenFile,
    ) {
        let read_allocation = pool.allocate(required);
        let read_bufs: Vec<bufpool::BufferPointer> = read_allocation.iter().collect();

        file.preadv(&read_bufs, read_index).unwrap();

        for read_buf in read_allocation.iter() {
            let observed = unsafe { std::slice::from_raw_parts(read_buf, BUFFER_SIZE as usize) };
            assert_eq!(buf, observed);
        }
    }

    mod lifecycle {
        use super::*;

        #[test]
        fn ok_new() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");

            let file_cfg = ffile::FrozenFileCfg {
                path,
                module_id: MODULE_ID,
                buffer_size: BUFFER_SIZE as usize,
                initial_available_buffers: INITIAL_BUFFER_AMOUT,
            };
            let file = sync::Arc::new(ffile::FrozenFile::new(file_cfg).unwrap());

            let pipe_cfg = WritePipeCfg { module_id: MODULE_ID, flush_duration: FLUSH_DURATION };
            assert!(WritePipe::new(pipe_cfg, file).is_ok());
        }

        #[test]
        fn ok_drop() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");
            let (_file, _, pipe) = new_objects(path);

            drop(pipe);
        }
    }

    mod shutdown {
        use super::*;

        #[test]
        fn ok_drop_before_pending_write_call() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");
            let (_file, pool, pipe) = new_objects(path);

            const BUFFER: [u8; BUFFER_SIZE as usize] = [0x20; BUFFER_SIZE as usize];

            let allocation = prep_write(BUFFER.as_ptr(), 1, &pool);
            let request = WriteRequest { allocation, slot_index: 0 };

            assert!(pipe.write(request).is_ok());
            drop(pipe);
        }

        #[test]
        fn ok_drop_waits_for_pending_write_call() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");

            const BUFFER: [u8; BUFFER_SIZE as usize] = [0x20; BUFFER_SIZE as usize];

            // new + write + drop
            {
                let (_file, pool, pipe) = new_objects(path.clone());

                let allocation = prep_write(BUFFER.as_ptr(), 1, &pool);
                let request = WriteRequest { allocation, slot_index: 0 };

                assert!(pipe.write(request).is_ok());
                drop(pipe);
            }

            // open + readback
            {
                let (file, pool, _) = new_objects(path);
                compare_with_readback(&BUFFER, 0, 1, &pool, &file);
            }
        }

        #[test]
        fn ok_drop_does_not_deadlock_when_multiple_pending_writes() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");
            let (_file, pool, pipe) = new_objects(path);

            for i in 0..INITIAL_BUFFER_AMOUT {
                let buffer = vec![i as u8; BUFFER_SIZE as usize];
                let allocation = prep_write(buffer.as_ptr(), 1, &pool);
                let request = WriteRequest { allocation, slot_index: 0 };

                assert!(pipe.write(request).is_ok());
            }

            drop(pipe);
        }

        #[test]
        fn ok_drop_correctly_waits_for_pending_write_with_multi_threads() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");
            let (_file, pool, pipe) = new_objects(path);

            const BUFFER: [u8; BUFFER_SIZE as usize] = [0x20; BUFFER_SIZE as usize];

            let pipe = sync::Arc::new(pipe);
            let pipe2 = sync::Arc::clone(&pipe);

            let handle = thread::spawn(move || {
                let allocation = prep_write(BUFFER.as_ptr(), 1, &pool);
                let request = WriteRequest { allocation, slot_index: 0 };

                assert!(pipe2.write(request).is_ok());
            });

            drop(pipe);
            handle.join().unwrap();
        }
    }

    mod pipe_writes {
        use super::*;

        #[test]
        fn ok_write() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");
            let (_file, pool, pipe) = new_objects(path);

            const BUFFER: [u8; BUFFER_SIZE as usize] = [0x0Au8; BUFFER_SIZE as usize];
            let allocation = prep_write(BUFFER.as_ptr(), 0x0A, &pool);

            let request = WriteRequest { allocation, slot_index: 0 };
            assert!(pipe.write(request).is_ok());
        }

        #[test]
        fn ok_write_epoch_is_monotonic() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");
            let (_file, pool, pipe) = new_objects(path);

            const BUFFER: [u8; BUFFER_SIZE as usize] = [0x0Au8; BUFFER_SIZE as usize];

            let allocation1 = prep_write(BUFFER.as_ptr(), 1, &pool);
            let ticket1 =
                pipe.write(WriteRequest { allocation: allocation1, slot_index: 0 }).unwrap();

            let allocation2 = prep_write(BUFFER.as_ptr(), 1, &pool);
            let ticket2 =
                pipe.write(WriteRequest { allocation: allocation2, slot_index: 1 }).unwrap();

            let allocation3 = prep_write(BUFFER.as_ptr(), 1, &pool);
            let ticket3 =
                pipe.write(WriteRequest { allocation: allocation3, slot_index: 2 }).unwrap();

            assert!(ticket3.epoch() > ticket2.epoch());
            assert!(ticket2.epoch() > ticket1.epoch());
        }
    }

    mod write_ticket {
        use super::*;

        #[test]
        fn ok_readback_after_write_with_await() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");
            let (file, pool, pipe) = new_objects(path);

            const REQUIRED: usize = 0x0A;
            const BUFFER: [u8; BUFFER_SIZE as usize] = [0x0Au8; BUFFER_SIZE as usize];

            let write_allocation = prep_write(BUFFER.as_ptr(), REQUIRED, &pool);
            let request = WriteRequest { allocation: write_allocation, slot_index: 0 };

            let ticket = pipe.write(request).unwrap();
            let ticket_epoch = ticket.epoch();

            let durable_epoch = futures::executor::block_on(ticket).unwrap();
            assert!(durable_epoch >= ticket_epoch);

            compare_with_readback(&BUFFER, 0, REQUIRED, &pool, &file);
        }

        #[test]
        fn ok_readback_after_batch_write() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");
            let (file, pool, pipe) = new_objects(path);

            const BUFFERS: [([u8; BUFFER_SIZE as usize], usize); 5] = [
                ([0x0Au8; BUFFER_SIZE as usize], 0x1A),
                ([0x0Bu8; BUFFER_SIZE as usize], 0x1B),
                ([0x0Cu8; BUFFER_SIZE as usize], 0x1C),
                ([0x0Du8; BUFFER_SIZE as usize], 0x1D),
                ([0x0Eu8; BUFFER_SIZE as usize], 0x1E),
            ];

            let mut slot_index = 0;
            let mut latest_ticket = None;

            for (buf, required) in BUFFERS {
                let allocation = prep_write(buf.as_ptr(), required, &pool);
                let request = WriteRequest { allocation, slot_index };
                let ticket = pipe.write(request).unwrap();

                slot_index += required;
                latest_ticket = Some(ticket);
            }

            assert!(latest_ticket.is_some());

            if let Some(ticket) = latest_ticket {
                let ticket_epoch = ticket.epoch();
                let durable_epoch = futures::executor::block_on(ticket).unwrap();

                assert!(durable_epoch >= ticket_epoch);
            }

            let mut read_index = 0;
            for (buf, required) in BUFFERS {
                compare_with_readback(&buf, read_index, required, &pool, &file);
                read_index += required;
            }
        }

        #[test]
        fn ok_multiple_concurrent_awaits() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("write_single");
            let (_file, pool, pipe) = new_objects(path);

            const REQUIRED: usize = 0x0A;
            const BUFFER: [u8; BUFFER_SIZE as usize] = [0x0Au8; BUFFER_SIZE as usize];

            let allocation1 = prep_write(BUFFER.as_ptr(), REQUIRED, &pool);
            let ticket1 =
                pipe.write(WriteRequest { allocation: allocation1, slot_index: 0 }).unwrap();

            let allocation2 = prep_write(BUFFER.as_ptr(), REQUIRED, &pool);
            let ticket2 =
                pipe.write(WriteRequest { allocation: allocation2, slot_index: 0 }).unwrap();

            let (e1, e2) = futures::executor::block_on(async { futures::join!(ticket1, ticket2) });

            assert!(e1.is_ok());
            assert!(e2.is_ok());
            assert!(e2.unwrap() > e1.unwrap());
        }

        #[test]
        fn ok_awaiting_last_ticket_implies_previous_writes_are_durable() {
            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("durability_boundary");

            let (file, pool, pipe) = new_objects(path);

            const BUFFER_A: [u8; BUFFER_SIZE as usize] = [0xAA; BUFFER_SIZE as usize];
            const BUFFER_B: [u8; BUFFER_SIZE as usize] = [0xBB; BUFFER_SIZE as usize];
            const BUFFER_C: [u8; BUFFER_SIZE as usize] = [0xCC; BUFFER_SIZE as usize];

            let alloc_a = prep_write(BUFFER_A.as_ptr(), 1, &pool);
            let ticket_a = pipe.write(WriteRequest { allocation: alloc_a, slot_index: 0 }).unwrap();

            let alloc_b = prep_write(BUFFER_B.as_ptr(), 1, &pool);
            let ticket_b = pipe.write(WriteRequest { allocation: alloc_b, slot_index: 1 }).unwrap();

            let alloc_c = prep_write(BUFFER_C.as_ptr(), 1, &pool);
            let ticket_c = pipe.write(WriteRequest { allocation: alloc_c, slot_index: 2 }).unwrap();

            let epoch_a = ticket_a.epoch();
            let epoch_b = ticket_b.epoch();
            let epoch_c = ticket_c.epoch();

            let durable_epoch = futures::executor::block_on(ticket_c).unwrap();
            assert!(durable_epoch >= epoch_c);
            assert!(durable_epoch >= epoch_b);
            assert!(durable_epoch >= epoch_a);

            compare_with_readback(&BUFFER_A, 0, 1, &pool, &file);
            compare_with_readback(&BUFFER_B, 1, 1, &pool, &file);
            compare_with_readback(&BUFFER_C, 2, 1, &pool, &file);
        }
    }

    mod concurrency {
        use super::*;

        #[test]
        fn ok_multi_threaded_writers() {
            const THREADS: usize = 4;
            const WRITES_PER_THREAD: usize = 0x40;
            const _: () = assert!(THREADS * WRITES_PER_THREAD < INITIAL_BUFFER_AMOUT);

            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("multi_threaded_writers");

            let (_file, pool, pipe) = new_objects(path);

            let pipe = sync::Arc::new(pipe);
            let pool = sync::Arc::new(pool);

            let mut handles = Vec::with_capacity(THREADS);
            for tid in 0..THREADS {
                let pipe = sync::Arc::clone(&pipe);
                let pool = sync::Arc::clone(&pool);

                handles.push(thread::spawn(move || {
                    let mut tickets = Vec::with_capacity(WRITES_PER_THREAD);

                    for i in 0..WRITES_PER_THREAD {
                        let buffer = vec![tid as u8; BUFFER_SIZE as usize];
                        let allocation = prep_write(buffer.as_ptr(), 1, &pool);
                        let slot_index = tid * WRITES_PER_THREAD + i;
                        let ticket = pipe.write(WriteRequest { allocation, slot_index }).unwrap();

                        tickets.push(ticket);
                    }

                    tickets
                }));
            }

            let mut tickets = Vec::new();
            for handle in handles {
                tickets.extend(handle.join().unwrap());
            }
            assert_eq!(tickets.len(), THREADS * WRITES_PER_THREAD,);

            let mut epochs: Vec<u64> = tickets.iter().map(ack::AckTicket::epoch).collect();
            epochs.sort_unstable();

            for (ed, observed) in (1u64..=epochs.len() as u64).zip(epochs.iter().copied()) {
                assert_eq!(ed, observed);
            }

            let latest_ticket = tickets.into_iter().max_by_key(ack::AckTicket::epoch).unwrap();
            let durable_epoch = futures::executor::block_on(latest_ticket).unwrap();
            assert_eq!(durable_epoch, (THREADS * WRITES_PER_THREAD) as u64,);
        }
    }

    mod parallel_listeners {
        use super::*;

        #[test]
        fn ok_many_parallel_waiters_same_durability_window() {
            const WAITERS: usize = 0x20;
            const BUFFER: [u8; BUFFER_SIZE as usize] = [0xAA; BUFFER_SIZE as usize];

            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("parallel_waiters");

            let (_file, pool, pipe) = new_objects(path);

            let mut tickets = Vec::with_capacity(WAITERS);
            for i in 0..WAITERS {
                let allocation = prep_write(BUFFER.as_ptr(), 1, &pool);
                let ticket = pipe.write(WriteRequest { allocation, slot_index: i }).unwrap();

                tickets.push(ticket);
            }

            let mut handles = Vec::with_capacity(WAITERS);
            for ticket in tickets {
                handles.push(thread::spawn(move || {
                    let epoch = ticket.epoch();
                    let durable_epoch = futures::executor::block_on(ticket).unwrap();

                    assert!(durable_epoch >= epoch);
                }));
            }

            for handle in handles {
                handle.join().unwrap();
            }
        }

        #[test]
        fn ok_parallel_waiters_multiple_batches() {
            const THREADS: usize = 0x0A;
            const WRITES: usize = 0x10;

            let dir = tempfile::tempdir().unwrap();
            let path = dir.path().join("parallel_batches");

            let (_file, pool, pipe) = new_objects(path);

            let pipe = sync::Arc::new(pipe);
            let pool = sync::Arc::new(pool);

            let mut handles = Vec::new();
            for tid in 0..THREADS {
                let pipe = pipe.clone();
                let pool = pool.clone();

                handles.push(thread::spawn(move || {
                    let buffer = [tid as u8; BUFFER_SIZE as usize];

                    for i in 0..WRITES {
                        let allocation = prep_write(buffer.as_ptr(), 1, &pool);
                        let ticket = pipe
                            .write(WriteRequest { allocation, slot_index: tid * WRITES + i })
                            .unwrap();

                        futures::executor::block_on(ticket).unwrap();
                    }
                }));
            }

            for handle in handles {
                handle.join().unwrap();
            }
        }
    }
}
