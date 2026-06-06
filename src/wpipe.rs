#![allow(missing_docs)]
#![allow(unused)]

use crate::{
    bufpool,
    error::{FrozenError, FrozenResult},
    ffile, hints, mpscq,
};
use std::{ptr, sync, sync::atomic, thread, time};

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

#[derive(Debug)]
pub struct WritePipe {
    cfg: WritePipeCfg,
    core: sync::Arc<Core>,
    flush_tx_handle: Option<thread::JoinHandle<()>>,
}

unsafe impl Send for WritePipe {}
unsafe impl Sync for WritePipe {}

impl WritePipe {
    pub fn new(cfg: WritePipeCfg, file: sync::Arc<ffile::FrozenFile>) -> FrozenResult<Self> {
        let core = sync::Arc::new(Core::new(file));
        let cloned_core = core.clone();
        let flush_tx_handle = match thread::Builder::new()
            .name("wpipe_flush_tx".into())
            .spawn(move || bg_flush_thread(cloned_core, cfg.flush_duration))
        {
            Ok(handle) => Some(handle),
            Err(observed_error) => return Err(err::new_error(cfg.module_id, err::FXE, observed_error)),
        };

        Ok(Self { cfg, core: core, flush_tx_handle })
    }

    #[inline]
    pub fn write(&self, allocation: bufpool::BufPoolAllocation, slot_index: usize) -> FrozenResult<u64> {
        let _io_lock = self.core.acquire_shared_io_lock();
        if let Some(frozen_error) = self.core.get_flush_error() {
            return Err(frozen_error);
        }

        let epoch = self.core.increment_current_epoch();
        let write_req = WriteRequest { allocation, slot_index, assigned_epoch: epoch };
        self.core.queue.push(write_req);

        Ok(epoch)
    }
}

impl Drop for WritePipe {
    fn drop(&mut self) {
        self.core.closed.store(true, atomic::Ordering::Release);
        self.core.flush_cv.notify_one();

        if let Some(handle) = self.flush_tx_handle.take() {
            let _ = handle.join();
        }

        // deallocate error memory (prevents memory leak)
        self.core.del_flush_error();
    }
}

/// ## Why we ignore [`std::sync::PoisonError`]?
///
/// The mutex used for lock, is solely used as a parking primitive for [`Condvar`] and does not protect any mutable
/// state. All the pool invariants and accounting are maintained via atomics and are completely seperated from
/// the mutex.
///
/// A poisoned mutex only indicates that another tx panicked while holding the lock, and indicates an inconsistent
/// state of the protected value. Since no state can be left partially modified under this lock, there is no
/// possible consistency risk to recover from and propagating the poison error would only introduce unnecessary
/// failures into the allocation path.
///
/// Therefore, as best effort, we consume the [`std::sync::PoisonError`] and continue operating with the recovered
/// guard.
fn bg_flush_thread(core: sync::Arc<Core>, flush_duration: time::Duration) {
    let mut guard = core.flush_guard.lock().unwrap_or_else(|e| e.into_inner());
    loop {
        (guard, _) = core.flush_cv.wait_timeout(guard, flush_duration).unwrap_or_else(|e| e.into_inner());

        let queued_ops = core.queue.drain();
        let closed = core.closed.load(atomic::Ordering::Acquire);

        if queued_ops.is_empty() {
            if closed {
                return;
            }

            continue;
        }

        let _io_lock = core.acquire_exclusive_io_lock();
        let (min_index, max_index, max_epoch) = match core.write_queued_ops(queued_ops) {
            Ok(res) => res,
            Err(frozen_error) => {
                core.set_flush_error(frozen_error);
                drop(_io_lock);

                continue;
            }
        };

        #[cfg(target_os = "linux")]
        if let Err(frozen_error) = core.file.sync_range(min_index, max_index - min_index) {
            core.set_flush_error(frozen_error);
            drop(_io_lock);

            continue;
        }

        match core.file.sync() {
            Err(frozen_error) => {
                core.set_flush_error(frozen_error);
                drop(_io_lock);

                continue;
            }
            Ok(_) => {
                core.mark_epoch_as_durable(max_epoch);
                core.del_flush_error();
            }
        }
    }
}

#[derive(Debug)]
struct Core {
    closed: atomic::AtomicBool,
    epoch: atomic::AtomicU64,
    durable_epoch: atomic::AtomicU64,
    file: sync::Arc<ffile::FrozenFile>,
    flush_cv: sync::Condvar,
    flush_error: atomic::AtomicPtr<FrozenError>,
    flush_guard: sync::Mutex<()>,
    io_lock: sync::RwLock<()>,
    queue: mpscq::MPSCQueue<WriteRequest>,
}

unsafe impl Send for Core {}

impl Core {
    fn new(file: sync::Arc<ffile::FrozenFile>) -> Self {
        Self {
            file,
            closed: atomic::AtomicBool::new(false),
            epoch: atomic::AtomicU64::new(0),
            durable_epoch: atomic::AtomicU64::new(0),
            flush_cv: sync::Condvar::new(),
            flush_error: atomic::AtomicPtr::new(ptr::null_mut()),
            flush_guard: sync::Mutex::new(()),
            io_lock: sync::RwLock::new(()),
            queue: mpscq::MPSCQueue::default(),
        }
    }

    #[inline]
    fn set_flush_error(&self, new_error: FrozenError) {
        let boxed_err = Box::into_raw(Box::new(new_error));
        let old_err = self.flush_error.swap(boxed_err, atomic::Ordering::AcqRel);

        if hints::unlikely(!old_err.is_null()) {
            unsafe {
                drop(Box::from_raw(old_err));
            }
        }
    }

    #[inline]
    fn get_flush_error(&self) -> Option<FrozenError> {
        let error_ptr = self.flush_error.load(atomic::Ordering::Acquire);
        if hints::likely(error_ptr.is_null()) {
            return None;
        }

        let frozen_error = unsafe { (*error_ptr).clone() };
        Some(frozen_error)
    }

    #[inline]
    fn del_flush_error(&self) {
        let old_error = self.flush_error.swap(ptr::null_mut(), atomic::Ordering::AcqRel);
        if hints::unlikely(!old_error.is_null()) {
            unsafe {
                drop(Box::from_raw(old_error));
            }
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
    fn write_queued_ops(&self, queued_ops: Vec<WriteRequest>) -> FrozenResult<(usize, usize, u64)> {
        let mut max_epoch = 0;
        let mut max_index = 0;
        let mut min_index = usize::MAX;

        for op in queued_ops {
            let ops_len = op.allocation.length();
            match ops_len {
                1 => {
                    self.file.pwrite(op.allocation.first(), op.slot_index)?;
                }
                _ => {
                    let bufs: Vec<bufpool::BufferPointer> = op.allocation.iter().collect();
                    self.file.pwritev(&bufs, op.slot_index)?;
                }
            }

            min_index = min_index.min(op.slot_index);
            max_epoch = max_epoch.max(op.assigned_epoch);
            max_index = max_index.max(op.slot_index + ops_len);
        }

        Ok((min_index, max_index, max_epoch))
    }

    #[inline]
    fn increment_current_epoch(&self) -> u64 {
        self.epoch.fetch_add(1, atomic::Ordering::AcqRel).wrapping_add(1)
    }

    #[inline]
    fn mark_epoch_as_durable(&self, epoch: u64) {
        self.durable_epoch.store(epoch, atomic::Ordering::Release);
    }
}

#[derive(Debug)]
struct WriteRequest {
    allocation: bufpool::BufPoolAllocation,
    assigned_epoch: u64,
    slot_index: usize,
}

mod err {
    use crate::error::{ErrCode, FrozenError};

    /// Domain ID for [`wpipe`] module is `0x02` used while propagating errors
    const DOMAIN_ID: u8 = 0x02;

    #[inline]
    pub fn new_error<E: std::fmt::Display>(module_id: u8, code: ErrCode, observed_error: E) -> FrozenError {
        FrozenError::new_raw(module_id, DOMAIN_ID, code, observed_error)
    }

    pub const FXE: ErrCode = ErrCode::new(0x10, "unable to spawn background flush thread");
}
