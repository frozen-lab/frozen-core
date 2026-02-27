//! Custom implementation of `mmap`

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::{
    error::{FrozenErr, FrozenRes},
    ffile::{FFCfg, FrozenFile},
    hints,
};
use std::{
    cell, fmt, mem,
    sync::{self, atomic},
    thread, time,
};

/// type for `epoch` used by write ops
type TEpoch = u64;

/// Domain Id for [`FrozenMMap`] is **18**
const ERRDOMAIN: u8 = 0x12;

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TMap = posix::POSIXMMap;

/// module id used for [`FrozenErr`]
static mut MODULE_ID: u8 = 0;

/// Error codes for [`FrozenMMap`]
#[repr(u16)]
pub enum FMMapErrRes {
    /// (512) internal fuck up (hault and catch fire)
    Hcf = 0x200,

    /// (513) unknown error (fallback)
    Unk = 0x201,

    /// (514) no more memory available
    Nmm = 0x202,

    /// (515) syncing error
    Syn = 0x203,

    /// (516) thread error or panic inside thread
    Txe = 0x204,

    /// (517) lock error (failed or poisoned)
    Lpn = 0x205,

    /// (518) perm error (read or write)
    Prm = 0x208,
}

impl FMMapErrRes {
    #[inline]
    fn default_message(&self) -> &'static [u8] {
        match self {
            Self::Lpn => b"lock poisoned",
            Self::Unk => b"unknown error type",
            Self::Nmm => b"no more memory left",
            Self::Hcf => b"hault and catch fire",
            Self::Prm => b"no perm to read or write",
            Self::Txe => b"thread failed or paniced",
            Self::Syn => b"failed to sync/flush data to storage device",
        }
    }
}

#[inline]
pub(in crate::fmmap) fn new_err<R>(res: FMMapErrRes, message: Vec<u8>) -> FrozenRes<R> {
    let detail = res.default_message();
    let err = FrozenErr::new(unsafe { MODULE_ID }, ERRDOMAIN, res as u16, detail, message);
    Err(err)
}

#[inline]
pub(in crate::fmmap) fn new_err_raw<E: std::fmt::Display>(res: FMMapErrRes, error: E) -> FrozenErr {
    let detail = res.default_message();
    FrozenErr::new(
        unsafe { MODULE_ID },
        ERRDOMAIN,
        res as u16,
        detail,
        error.to_string().as_bytes().to_vec(),
    )
}

/// Custom implementation of `mmap`
#[derive(Debug)]
pub struct FrozenMMap<T>
where
    T: Sized + Send + Sync,
{
    core: sync::Arc<Core>,
    tx: Option<thread::JoinHandle<()>>,
    _type: core::marker::PhantomData<T>,
}

unsafe impl<T> Send for FrozenMMap<T> where T: Sized + Send + Sync {}
unsafe impl<T> Sync for FrozenMMap<T> where T: Sized + Send + Sync {}

impl<T> FrozenMMap<T>
where
    T: Sized + Send + Sync,
{
    const SLOT_SIZE: usize = std::mem::size_of::<ObjectInterface<T>>();

    /// Read current length of [`FrozenMMap`]
    #[inline]
    pub fn length(&self) -> usize {
        self.core.curr_length()
    }

    /// Create a new [`FrozenMMap`] instance w/ given [`FFCfg`]
    ///
    /// ## [`FFCfg`]
    ///
    /// All configs for [`FrozenFile`] are stored in [`FFCfg`]
    ///
    /// ## Working
    ///
    /// We first create a new [`FrozenFile`] if note already, then map the entire file using `mmap(2)`,
    /// the entire file must read/write `T`, which also should stay constant for the entire lifetime of file
    ///
    /// ## Important
    ///
    /// The `cfg` must not change any of its properties for the entire life of [`FrozenFile`],
    /// which is used under the hood, one must use config stores like [`Rta`](https://crates.io/crates/rta)
    /// to store config
    ///
    /// ## Multiple Instances
    ///
    /// We acquire an exclusive lock for the entire file, this protects against operating with
    /// multiple simultenious instance of [`FrozenFile`], when trying to call [`FrozenFile::new`]
    /// when already called, [`FFileErrRes::Lck`] error will be thrown
    pub fn new(cfg: FFCfg, flush_duration: time::Duration) -> FrozenRes<Self> {
        let mid = cfg.mid;
        let file = FrozenFile::new(cfg)?;
        let curr_length = file.length()?;

        // NOTE: we only set it the module_id once, right after an exclusive lock for the entire file is
        // acquired, hence it'll be only set once per instance and is only used for error logging
        unsafe { MODULE_ID = mid };

        let mmap = unsafe { TMap::new(file.fd(), curr_length) }?;
        let core = sync::Arc::new(Core::new(mmap, file, flush_duration, curr_length));

        // INFO: we spawn the thread for background sync
        let tx = Core::spawn_tx(core.clone())?;

        Ok(Self {
            core,
            tx: Some(tx),
            _type: core::marker::PhantomData,
        })
    }

    /// Returns the [`FrozenErr`] representing the last error occurred in [`FrozenMMap`]
    #[inline]
    pub fn last_error(&self) -> Option<FrozenErr> {
        self.core.get_sync_error()
    }

    /// Wait for durability for the given write `epoch`
    ///
    /// This functions blocks until epoch becomes durable
    pub fn wait_for_durability(&self, epoch: u64) -> FrozenRes<()> {
        let durable_epoch = self.core.durable_epoch.load(atomic::Ordering::Acquire);
        if durable_epoch == 0 || durable_epoch > epoch {
            return Ok(());
        }

        let mut guard = match self.core.durable_lock.lock() {
            Ok(g) => g,
            Err(e) => return Err(new_err_raw(FMMapErrRes::Lpn, e)),
        };

        loop {
            if self.core.durable_epoch.load(atomic::Ordering::Acquire) > epoch {
                return Ok(());
            }

            guard = match self.core.durable_cv.wait(guard) {
                Ok(g) => g,
                Err(e) => return Err(new_err_raw(FMMapErrRes::Lpn, e)),
            };
        }
    }

    /// Get's a read only typed pointer for `T`
    #[inline]
    pub fn read<R>(&self, index: usize, f: impl FnOnce(&T) -> R) -> FrozenRes<R> {
        let offset = Self::SLOT_SIZE * index;
        let _guard = self.core.acquire_io_lock()?;

        let slot = unsafe { &*self.get_mmap().as_ptr::<T>(offset) };
        let _oi_guard = slot.lock();
        let res = unsafe { f(slot.get()) };

        Ok(res)
    }

    /// Get's a mutable typed pointer for `T`
    #[inline]
    pub fn write<R>(&self, index: usize, f: impl FnOnce(&mut T) -> R) -> FrozenRes<(R, TEpoch)> {
        let offset = Self::SLOT_SIZE * index;
        let _guard = self.core.acquire_io_lock()?;

        let slot = unsafe { &*self.get_mmap().as_ptr::<T>(offset) };
        let _oi_guard = slot.lock();
        let res = unsafe { f(slot.get_mut()) };

        let epoch = self.core.durable_epoch.load(atomic::Ordering::Acquire);
        self.core.dirty.store(true, atomic::Ordering::Release);

        Ok((res, epoch))
    }

    /// Grow [`FrozenMMap`] by given `count` of `T`
    ///
    /// We first grow underlying [`FrozenFile`] and then re-mmap including the grown region
    pub fn grow(&self, count: usize) -> FrozenRes<()> {
        let core = &self.core;
        let len_to_add = count * Self::SLOT_SIZE;

        // pause all read, write and bg sync ops while growing
        let _lock = self.core.acquire_exclusive_io_lock()?;

        // swap dirty flag and manual sync to avoid any kind of data loss before unmap
        if core.dirty.swap(false, atomic::Ordering::AcqRel) {
            core.sync()?;
        }

        unsafe {
            let mmap = &mut *core.mmap.get();
            mem::ManuallyDrop::drop(mmap);
        }

        core.ffile.grow(len_to_add)?;

        let new_len = core.ffile.length()?;
        core.curr_length.store(new_len, atomic::Ordering::Release);

        unsafe {
            let new_map = TMap::new(core.ffile.fd(), new_len)?;
            *core.mmap.get() = mem::ManuallyDrop::new(new_map);
        };

        Ok(())
    }

    #[inline]
    fn munmap(&self) -> FrozenRes<()> {
        let length = self.length();
        unsafe { self.get_mmap().unmap(length) }
    }

    #[inline]
    fn get_mmap(&self) -> &mem::ManuallyDrop<TMap> {
        unsafe { &*self.core.mmap.get() }
    }
}

impl<T> Drop for FrozenMMap<T>
where
    T: Sized + Send + Sync,
{
    fn drop(&mut self) {
        // INFO: we must acquire an exclusive lock, to prevent dropping while sync,
        // growing or any read/write ops
        let _io_lock = self
            .core
            .acquire_exclusive_io_lock()
            .expect("io_lock poisoned during FrozenMMap::drop");

        // close flusher thread
        self.core.closed.store(true, atomic::Ordering::Release);
        self.core.cv.notify_one();

        if let Some(handle) = self.tx.take() {
            handle.join().expect("flush thread panicked during FrozenMMap::drop");
        }

        // sync if dirty
        if self.core.dirty.swap(false, atomic::Ordering::AcqRel) {
            let _ = self.core.sync();
        }

        // free up the boxed error (if any)
        let ptr = self.core.error.load(atomic::Ordering::Acquire);
        if !ptr.is_null() {
            unsafe {
                drop(Box::from_raw(ptr));
            }
        }

        let _ = self.munmap();
    }
}

impl<T> fmt::Display for FrozenMMap<T>
where
    T: Sized + Send + Sync,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FrozenMMap{{fd: {}, len: {}}}", self.core.ffile.fd(), self.length())
    }
}

#[derive(Debug)]
struct Core {
    cv: sync::Condvar,
    ffile: FrozenFile,
    lock: sync::Mutex<()>,
    io_lock: sync::RwLock<()>,
    dirty: atomic::AtomicBool,
    durable_cv: sync::Condvar,
    closed: atomic::AtomicBool,
    durable_lock: sync::Mutex<()>,
    flush_duration: time::Duration,
    durable_epoch: atomic::AtomicU64,
    curr_length: atomic::AtomicUsize,
    error: atomic::AtomicPtr<FrozenErr>,
    mmap: cell::UnsafeCell<mem::ManuallyDrop<TMap>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(mmap: TMap, ffile: FrozenFile, flush_duration: time::Duration, curr_length: usize) -> Self {
        Self {
            ffile,
            flush_duration,
            cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            io_lock: sync::RwLock::new(()),
            durable_cv: sync::Condvar::new(),
            durable_lock: sync::Mutex::new(()),
            dirty: atomic::AtomicBool::new(false),
            closed: atomic::AtomicBool::new(false),
            durable_epoch: atomic::AtomicU64::new(0),
            curr_length: atomic::AtomicUsize::new(curr_length),
            error: atomic::AtomicPtr::new(std::ptr::null_mut()),
            mmap: cell::UnsafeCell::new(mem::ManuallyDrop::new(mmap)),
        }
    }

    #[inline]
    fn curr_length(&self) -> usize {
        self.curr_length.load(atomic::Ordering::Acquire)
    }

    #[inline]
    fn sync(&self) -> FrozenRes<()> {
        unsafe { (*self.mmap.get()).sync(self.curr_length()) }?;
        self.ffile.sync()
    }

    #[inline]
    fn set_sync_error(&self, err: FrozenErr) {
        let boxed = Box::into_raw(Box::new(err));
        let old = self.error.swap(boxed, atomic::Ordering::AcqRel);

        // NOTE: we must free the old error if any to avoid leaks
        if !old.is_null() {
            unsafe {
                drop(Box::from_raw(old));
            }
        }
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
    fn clear_sync_error(&self) {
        let old = self.error.swap(std::ptr::null_mut(), atomic::Ordering::AcqRel);
        if hints::unlikely(!old.is_null()) {
            unsafe {
                drop(Box::from_raw(old));
            }
        }
    }

    #[inline]
    fn acquire_io_lock(&self) -> FrozenRes<sync::RwLockReadGuard<'_, ()>> {
        self.io_lock.read().map_err(|e| new_err_raw(FMMapErrRes::Lpn, e))
    }

    #[inline]
    fn acquire_exclusive_io_lock(&self) -> FrozenRes<sync::RwLockWriteGuard<'_, ()>> {
        self.io_lock.write().map_err(|e| new_err_raw(FMMapErrRes::Lpn, e))
    }

    fn spawn_tx(core: sync::Arc<Self>) -> FrozenRes<thread::JoinHandle<()>> {
        match thread::Builder::new()
            .name("fm-flush-tx".into())
            .spawn(move || Self::tx_thread(core))
        {
            Ok(tx) => Ok(tx),
            Err(error) => {
                let mut error = error.to_string().as_bytes().to_vec();
                error.extend_from_slice(b"Failed to spawn flush thread for FrozenMMap");
                new_err(FMMapErrRes::Hcf, error)
            }
        }
    }

    fn tx_thread(core: sync::Arc<Self>) {
        // init phase (acquiring locks)
        let mut guard = match core.lock.lock() {
            Ok(g) => g,
            Err(error) => {
                let mut message = error.to_string().as_bytes().to_vec();
                message.extend_from_slice(b"Flush thread died before init could be completed for FrozenMMap");
                let error = FrozenErr::new(
                    unsafe { MODULE_ID },
                    ERRDOMAIN,
                    FMMapErrRes::Lpn as u16,
                    FMMapErrRes::Lpn.default_message(),
                    message,
                );
                core.set_sync_error(error);
                return;
            }
        };

        // sync loop w/ non-busy waiting
        loop {
            guard = match core.cv.wait_timeout(guard, core.flush_duration) {
                Ok((g, _)) => g,
                Err(e) => {
                    core.set_sync_error(new_err_raw(FMMapErrRes::Txe, e));
                    return;
                }
            };

            // we must close the thread when [`FrozenMMap`] is closed
            if hints::unlikely(core.closed.load(atomic::Ordering::Acquire)) {
                return;
            }

            // this helps us avoid sync when no data is updated
            if hints::likely(core.dirty.swap(false, atomic::Ordering::AcqRel) == false) {
                continue;
            }

            // INFO: we must acquire an exclusive IO lock for sync, hence no write, read or
            // grow could kick in while sync is in progress

            let io_lock = match core.acquire_exclusive_io_lock() {
                Ok(lock) => lock,
                Err(e) => {
                    core.set_sync_error(new_err_raw(FMMapErrRes::Lpn, e));
                    return;
                }
            };

            // INFO: we must drop the guard before syscall, as its a blocking operation and holding
            // the mutex while the syscall takes place is not a good idea, while we drop the mutex
            // and acqurie it again, in-between other process could acquire it and use it
            drop(guard);

            // NOTE:
            //
            // - if sync fails, we update the Core::error w/ the received error object
            // - we clear it up when another sync call succeeds
            // - this is valid, as the underlying sync flushes entire mmaped region, hence
            //   even if the last call failed, and the new one succeeded, we do get the durability
            //   guarenty for the old data as well

            match core.sync() {
                Ok(_) => {
                    core.durable_epoch.fetch_add(1, atomic::Ordering::Release);

                    let _g = match core.durable_lock.lock() {
                        Ok(g) => g,
                        Err(e) => {
                            core.set_sync_error(new_err_raw(FMMapErrRes::Lpn, e));
                            return;
                        }
                    };

                    core.durable_cv.notify_all();
                    core.clear_sync_error();
                }
                Err(err) => core.set_sync_error(err),
            }

            drop(io_lock);
            guard = match core.lock.lock() {
                Ok(g) => g,
                Err(e) => {
                    core.set_sync_error(new_err_raw(FMMapErrRes::Lpn, e));
                    return;
                }
            };
        }
    }
}

#[repr(C, align(0x40))]
pub(in crate::fmmap) struct ObjectInterface<T>
where
    T: Sized + Send + Sync,
{
    lock: atomic::AtomicU8,
    value: cell::UnsafeCell<T>,
}

impl<T> ObjectInterface<T>
where
    T: Sized + Send + Sync,
{
    const MAX_SPINS: usize = 0x10;

    #[inline]
    fn lock(&self) -> OIGuard<'_, T> {
        let mut spins = 0;
        loop {
            if self
                .lock
                .compare_exchange_weak(0, 1, atomic::Ordering::Acquire, atomic::Ordering::Relaxed)
                .is_ok()
            {
                return OIGuard { oi: self };
            }

            if hints::likely(spins < Self::MAX_SPINS) {
                std::hint::spin_loop();
            } else {
                std::thread::yield_now();
            }

            spins += 1;
        }
    }

    #[inline]
    unsafe fn get(&self) -> &T {
        &*self.value.get()
    }

    #[inline]
    unsafe fn get_mut(&self) -> &mut T {
        &mut *self.value.get()
    }
}

struct OIGuard<'a, T>
where
    T: Sized + Send + Sync,
{
    oi: &'a ObjectInterface<T>,
}

impl<'a, T> Drop for OIGuard<'a, T>
where
    T: Sized + Send + Sync,
{
    fn drop(&mut self) {
        self.oi.lock.store(0, atomic::Ordering::Release);
    }
}
