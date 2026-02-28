//! Custom implementation of `mmap(2)`
//!
//! ## Example
//!
//! ```
//! use frozen_core::fmmap::{FrozenMMap, FMCfg};
//!
//! let dir = tempfile::tempdir().unwrap();
//! let path = dir.path().join("tmp_frozen_mmap");
//!
//! let cfg = FMCfg {
//!     path,
//!     mid: 0u8,
//!     initial_count: 0x0A,
//!     flush_duration: std::time::Duration::from_micros(100),
//! };
//!
//! let mmap = FrozenMMap::<u64>::new(cfg.clone()).unwrap();
//! assert_eq!(mmap.slots(), 0x0A);
//!
//! let (_, epoch) = mmap.write(0, |v| *v = 0xDEADC0DE).unwrap();
//! mmap.wait_for_durability(epoch).unwrap();
//!
//! let val = mmap.read(0, |v| *v).unwrap();
//! assert_eq!(val, 0xDEADC0DE);
//!
//! mmap.grow(0x05).unwrap();
//! assert_eq!(mmap.slots(), 0x0A + 0x05);
//!
//! drop(mmap);
//!
//! let reopened = FrozenMMap::<u64>::new(cfg).unwrap();
//! let val = reopened.read(0, |v| *v).unwrap();
//! assert_eq!(val, 0xDEADC0DE);
//! ```

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

    /// (519) invalid cfg
    Cfg = 0x209,
}

impl FMMapErrRes {
    #[inline]
    fn default_message(&self) -> &'static [u8] {
        match self {
            Self::Cfg => b"invalid cfg",
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

/// Config for [`FrozenMMap`]
#[derive(Debug, Clone)]
pub struct FMCfg {
    /// Module id used for error logging
    pub mid: u8,

    /// Path for the underlying file
    ///
    /// *NOTE:* The caller must make sure that the parent directory exists
    pub path: std::path::PathBuf,

    /// Number of slots to pre-allocate when [`FrozenMMap`] is initialized
    ///
    /// Each slot has size of [`FrozenMMap::<T>::SLOT_SIZE`], where initial file length will
    /// be `chunk_size * initial_count` (bytes)
    pub initial_count: usize,

    /// Time interval used by flusher tx, to batch write ops into a durable window and sync them
    /// together, where all write ops in certain time interval falls into a single durable window
    pub flush_duration: time::Duration,
}

/// Custom implementation of `mmap(2)`
///
/// ## Example
///
/// ```
/// use frozen_core::fmmap::{FrozenMMap, FMCfg};
///
/// let dir = tempfile::tempdir().unwrap();
/// let path = dir.path().join("tmp_frozen_mmap");
///
/// let cfg = FMCfg {
///     path,
///     mid: 0u8,
///     initial_count: 0x0A,
///     flush_duration: std::time::Duration::from_micros(100),
/// };
///
/// let mmap = FrozenMMap::<u64>::new(cfg.clone()).unwrap();
/// assert_eq!(mmap.slots(), 0x0A);
///
/// let (_, epoch) = mmap.write(0, |v| *v = 0xDEADC0DE).unwrap();
/// mmap.wait_for_durability(epoch).unwrap();
///
/// let val = mmap.read(0, |v| *v).unwrap();
/// assert_eq!(val, 0xDEADC0DE);
///
/// mmap.grow(0x05).unwrap();
/// assert_eq!(mmap.slots(), 0x0A + 0x05);
///
/// drop(mmap);
///
/// let reopened = FrozenMMap::<u64>::new(cfg).unwrap();
/// let val = reopened.read(0, |v| *v).unwrap();
/// assert_eq!(val, 0xDEADC0DE);
/// ```
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
    /// Memory space required for each slot of [`T`] in [`FrozenMMap`]
    pub const SLOT_SIZE: usize = std::mem::size_of::<ObjectInterface<T>>();

    /// Read current count of slots in [`FrozenMMap`], where each slot has size of [`FrozenMMap::<T>::SLOT_SIZE`]
    #[inline]
    pub fn slots(&self) -> usize {
        self.core.curr_length() / Self::SLOT_SIZE
    }

    /// Create a new [`FrozenMMap`] instance w/ given [`FMCfg`]
    ///
    /// ## [`FMCfg`]
    ///
    /// All configs for [`FrozenMMap`] are stored in [`FMCfg`]
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
    pub fn new(cfg: FMCfg) -> FrozenRes<Self> {
        let ff_cfg = FFCfg {
            mid: cfg.mid,
            path: cfg.path,
            chunk_size: Self::SLOT_SIZE,
            initial_chunk_amount: cfg.initial_count,
        };

        let file = FrozenFile::new(ff_cfg)?;
        let curr_length = file.length()?;

        // NOTE: we only set it the module_id once, right after an exclusive lock for the entire file is
        // acquired, hence it'll be only set once per instance and is only used for error logging
        unsafe { MODULE_ID = cfg.mid };

        let mmap = unsafe { TMap::new(file.fd(), curr_length) }?;
        let core = sync::Arc::new(Core::new(mmap, file, cfg.flush_duration, curr_length));

        // INFO: we spawn the thread for background sync
        let tx = Core::spawn_tx(core.clone())?;

        Ok(Self {
            core,
            tx: Some(tx),
            _type: core::marker::PhantomData,
        })
    }

    /// Blocks until given `epoch` becomes durable
    ///
    /// ## Batching
    ///
    /// With respect to `flush_duration`, all write ops are batched before sync, which is executed by flusher tx
    /// working in background, while each write is assigned w/ current durable epoch, and all writes which
    /// observe the exact same epoch, belong to the same durability window, and are all sync'ed together
    ///
    /// When a background sync succeeds, the internal durable epoch is incremented, indicating that all writes
    /// that observed the previous epoch are now durable on disk
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_wait_epoch");
    ///
    /// let cfg = FMCfg {
    ///     path,
    ///     mid: 0u8,
    ///     initial_count: 0x04,
    ///     flush_duration: std::time::Duration::from_micros(100),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(cfg).unwrap();
    ///
    /// let (_, epoch) = mmap.write(0, |v| *v = 123).unwrap();
    /// mmap.wait_for_durability(epoch).unwrap();
    ///
    /// let val = mmap.read(0, |v| *v).unwrap();
    /// assert_eq!(val, 123);
    /// ```
    pub fn wait_for_durability(&self, epoch: u64) -> FrozenRes<()> {
        if let Some(sync_err) = self.core.get_sync_error() {
            return Err(sync_err);
        }

        let durable_epoch = self.core.durable_epoch.load(atomic::Ordering::Acquire);
        if durable_epoch == 0 || durable_epoch > epoch {
            return Ok(());
        }

        let mut guard = match self.core.durable_lock.lock() {
            Ok(g) => g,
            Err(e) => return Err(new_err_raw(FMMapErrRes::Lpn, e)),
        };

        loop {
            if let Some(sync_err) = self.core.get_sync_error() {
                return Err(sync_err);
            }

            if self.core.durable_epoch.load(atomic::Ordering::Acquire) > epoch {
                return Ok(());
            }

            guard = match self.core.durable_cv.wait(guard) {
                Ok(g) => g,
                Err(e) => return Err(new_err_raw(FMMapErrRes::Lpn, e)),
            };
        }
    }

    /// Read a `T` at given `index` via callback (`f`)
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_read_mmap");
    ///
    /// let cfg = FMCfg {
    ///     path,
    ///     mid: 0u8,
    ///     initial_count: 0x02,
    ///     flush_duration: std::time::Duration::from_micros(100),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(cfg).unwrap();
    /// mmap.write(0, |v| *v = 0x0A).unwrap();
    ///
    /// let val = mmap.read(0, |v| *v).unwrap();
    /// assert_eq!(val, 0x0A);
    /// ```
    #[inline]
    pub fn read<R>(&self, index: usize, f: impl FnOnce(&T) -> R) -> FrozenRes<R> {
        let offset = Self::SLOT_SIZE * index;
        let _guard = self.core.acquire_io_lock()?;

        let slot = unsafe { &*self.get_mmap().as_ptr::<T>(offset) };
        let _oi_guard = slot.lock();
        let res = unsafe { f(slot.get()) };

        Ok(res)
    }

    /// Write/update a `T` at given `index` via callback (`f`)
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_write_mmap");
    ///
    /// let cfg = FMCfg {
    ///     path,
    ///     mid: 0u8,
    ///     initial_count: 0x02,
    ///     flush_duration: std::time::Duration::from_micros(100),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(cfg).unwrap();
    ///
    /// let (_, epoch) = mmap.write(1, |v| *v = 0x2B).unwrap();
    /// mmap.wait_for_durability(epoch).unwrap();
    ///
    /// let val = mmap.read(1, |v| *v).unwrap();
    /// assert_eq!(val, 0x2B);
    /// ```
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

    /// Grow [`FrozenMMap`] by given `slot_count` of `T`, where each slot has size of [`FrozenMMap::<T>::SLOT_SIZE`]
    ///
    /// ## Working
    ///
    /// When `grow` is called, all read, write, and (background) sync ops are paused till completion,
    /// growth is done in following steps:
    ///
    /// - acquire an exclusive `io_lock` (all other ops are paused)
    /// - if any batch is pending for sync,
    ///   - swap the flag
    ///   - call sync manually
    ///   - incr epoch and update cv
    /// - `munmap(2)` current mapping
    /// - grow underlying [`FrozenFile`] by requested `count` via [`FrozenFile::grow`]
    /// - `mmap(2)` entire file again
    /// - free the lock and unpause all ops
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_grow_mmap");
    ///
    /// let cfg = FMCfg {
    ///     mid: 0u8,
    ///     path,
    ///     initial_count: 0x02,
    ///     flush_duration: std::time::Duration::from_micros(100),
    /// };
    ///
    /// let mmap = FrozenMMap::<u64>::new(cfg).unwrap();
    /// assert_eq!(mmap.slots(), 0x02);
    ///
    /// mmap.grow(0x03).unwrap();
    /// assert_eq!(mmap.slots(), 0x05);
    ///
    /// let idx = mmap.slots() - 1;
    /// mmap.write(idx, |v| *v = 0x100).unwrap();
    ///
    /// let val = mmap.read(idx, |v| *v).unwrap();
    /// assert_eq!(val, 0x100);
    /// ```
    pub fn grow(&self, count: usize) -> FrozenRes<()> {
        let core = &self.core;

        // pause all read, write and bg sync ops while growing
        let _lock = self.core.acquire_exclusive_io_lock()?;

        // swap dirty flag and manual sync to avoid any kind of data loss before unmap
        if core.dirty.swap(false, atomic::Ordering::AcqRel) {
            core.sync()?;
            core.incr_epoch();

            let _g = core.durable_lock.lock().map_err(|e| new_err_raw(FMMapErrRes::Lpn, e))?;
            core.durable_cv.notify_all();
        }

        // unmap the current mmap and clear unsafeCell
        unsafe {
            self.munmap()?;
            mem::ManuallyDrop::drop(&mut *core.mmap.get());
        }

        core.ffile.grow(count)?;

        let new_len = core.ffile.length()?;
        core.curr_length.store(new_len, atomic::Ordering::Release);

        unsafe {
            let new_map = TMap::new(core.ffile.fd(), new_len)?;
            *core.mmap.get() = mem::ManuallyDrop::new(new_map);
        };

        Ok(())
    }

    /// Delete the underlying [`FrozenFile`] used for [`FrozenMMap`] from fs
    ///
    /// ## Working
    ///
    /// When `delete` is called, all read, write, and (background) sync ops are paused (indefinitely),
    /// whule deletion is done with following steps:
    ///
    /// - acquire an exclusive `io_lock` (all other ops are paused indefinitely)
    /// - if any batch is pending for sync,
    ///   - swap the flag
    ///   - call sync manually
    ///   - incr epoch and update cv
    /// - brodcast closing so flusher tx could wrap up
    /// - `munmap(2)` current mapping
    /// - call delete on [`FrozenFile`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::fmmap::{FrozenMMap, FMCfg};
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_delete_mmap");
    ///
    /// let cfg = FMCfg {
    ///     mid: 0u8,
    ///     path: path.clone(),
    ///     initial_count: 0x04,
    ///     flush_duration: std::time::Duration::from_micros(100),
    /// };
    ///
    /// let mut mmap = FrozenMMap::<u64>::new(cfg).unwrap();
    ///
    /// mmap.write(0, |v| *v = 55).unwrap();
    /// mmap.delete().unwrap();
    /// assert!(!path.exists());
    /// ```
    pub fn delete(&mut self) -> FrozenRes<()> {
        let core = &self.core;

        // pause all read, write and bg sync ops while growing
        let _lock = core.acquire_exclusive_io_lock()?;

        // swap dirty flag and manual sync to avoid any kind of data loss before unmap
        if core.dirty.swap(false, atomic::Ordering::AcqRel) {
            core.sync()?;
            core.incr_epoch();

            let _g = core.durable_lock.lock().map_err(|e| new_err_raw(FMMapErrRes::Lpn, e))?;
            core.durable_cv.notify_all();
        }

        // NOTE: we must broadcast that the close is happening to allow flusher tx to wrap up
        core.closed.store(true, atomic::Ordering::Release);
        core.cv.notify_one();

        if let Some(handle) = self.tx.take() {
            let _ = handle.join();
        }

        self.munmap()?;
        core.ffile.delete()
    }

    #[inline]
    fn munmap(&self) -> FrozenRes<()> {
        let length = self.core.curr_length();
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
        // safeguard aginst `delete()` or drop-on-drop (if somehow its possible)
        let not_unmapped = !self.core.closed.swap(true, atomic::Ordering::Release);
        self.core.cv.notify_one(); // notify flusher tx to shut

        if let Some(handle) = self.tx.take() {
            let _ = handle.join();
        }

        // INFO: we must acquire an exclusive lock, to prevent dropping while sync,
        // growing or any read/write ops
        let _io_lock = self.core.acquire_exclusive_io_lock();

        // sync if dirty
        if not_unmapped && self.core.dirty.swap(false, atomic::Ordering::AcqRel) {
            let _ = self.core.sync();
        }

        // free up the boxed error (if any)
        let ptr = self.core.error.load(atomic::Ordering::Acquire);
        if !ptr.is_null() {
            unsafe {
                drop(Box::from_raw(ptr));
            }
        }

        if not_unmapped {
            let _ = self.munmap();
        }
    }
}

impl<T> fmt::Display for FrozenMMap<T>
where
    T: Sized + Send + Sync,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FrozenMMap{{fd: {}, len: {}}}",
            self.core.ffile.fd(),
            self.core.curr_length()
        )
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

        // NOTE: we must free the old error, if any, to avoid mem leaks
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

    #[inline]
    fn incr_epoch(&self) {
        self.durable_epoch.fetch_add(1, atomic::Ordering::Release);
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

            // NOTE: we must read values of close and dirty brodcast before acquire exclusive lock,
            // if done otherwise, we impose serious deadlock sort of situation for the the flusher tx

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
                    core.incr_epoch();

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::TEST_MID;
    use crate::ffile::FFileErrRes;

    const INIT_SLOTS: usize = 0x0A;

    // NOTE: we keep this small on purpose, so we won't have to wait at all in tests
    const FLUSH_DURATION: time::Duration = time::Duration::from_micros(10);

    fn new_tmp() -> (tempfile::TempDir, FMCfg) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tmp_map");

        let cfg = FMCfg {
            path,
            mid: TEST_MID,
            initial_count: INIT_SLOTS,
            flush_duration: FLUSH_DURATION,
        };

        (dir, cfg)
    }

    mod fm_lifecycle {
        use super::*;

        #[test]
        fn ok_new() {
            let (_dir, cfg) = new_tmp();
            let mmap = FrozenMMap::<u8>::new(cfg).unwrap();

            assert_eq!(mmap.core.flush_duration, FLUSH_DURATION);
            assert!(!mmap.core.dirty.load(atomic::Ordering::Acquire));
            assert!(!mmap.core.closed.load(atomic::Ordering::Acquire));
            assert_eq!(mmap.core.durable_epoch.load(atomic::Ordering::Acquire), 0);
            assert_eq!(
                mmap.core.curr_length.load(atomic::Ordering::Acquire),
                INIT_SLOTS * FrozenMMap::<u8>::SLOT_SIZE
            );

            // satisfies the bg thread was spawned correctly
            assert!(mmap.core.error.load(atomic::Ordering::Acquire).is_null());

            // satisfies wait on epoch works
            assert!(mmap.wait_for_durability(0).is_ok());
        }

        #[test]
        fn ok_new_existing() {
            let (_dir, cfg) = new_tmp();

            // create new + close
            let mmap1 = FrozenMMap::<u8>::new(cfg.clone()).unwrap();
            drop(mmap1);

            // open existing
            let mmap2 = FrozenMMap::<u8>::new(cfg).unwrap();
            drop(mmap2);
        }

        #[test]
        fn err_new_when_change_in_cfg() {
            let (_dir, mut cfg) = new_tmp();

            // create new + close
            let mmap1 = FrozenMMap::<u8>::new(cfg.clone()).unwrap();
            drop(mmap1);

            // update cfg + opne existing
            cfg.initial_count = INIT_SLOTS * 2;
            let err = FrozenMMap::<u8>::new(cfg).unwrap_err();
            assert!(err.cmp(FFileErrRes::Cpt as u16));
        }

        #[test]
        fn ok_delete() {
            let (_dir, cfg) = new_tmp();
            let mut mmap = FrozenMMap::<u8>::new(cfg.clone()).unwrap();

            mmap.delete().unwrap();
            assert!(!mmap.core.ffile.exists().unwrap());
        }

        #[test]
        fn err_delete_after_delete() {
            let (_dir, cfg) = new_tmp();
            let mut mmap = FrozenMMap::<u8>::new(cfg.clone()).unwrap();

            mmap.delete().unwrap();
            assert!(!mmap.core.ffile.exists().unwrap());

            let err = mmap.delete().unwrap_err();
            assert!(err.cmp(FFileErrRes::Inv as u16));
        }

        #[test]
        fn ok_drop_persists_when_dropped_before_bg_flush() {
            let (_dir, cfg) = new_tmp();
            const VAL: u8 = 0x0A;

            {
                let mmap = FrozenMMap::<u8>::new(cfg.clone()).unwrap();
                mmap.write(0, |byte| *byte = VAL).unwrap();
                drop(mmap);
            }

            {
                let mmap = FrozenMMap::<u8>::new(cfg.clone()).unwrap();
                let val = mmap.read(0, |byte| *byte).unwrap();
                assert_eq!(val, VAL);
            }
        }
    }

    mod fm_grow {
        use super::*;

        #[test]
        fn ok_grow_updates_length() {
            let (_dir, cfg) = new_tmp();
            let mmap = FrozenMMap::<u8>::new(cfg).unwrap();
            assert_eq!(mmap.core.curr_length(), INIT_SLOTS * FrozenMMap::<u8>::SLOT_SIZE);

            mmap.grow(0x0A).unwrap();
            assert_eq!(
                mmap.core.curr_length(),
                (INIT_SLOTS + 0x0A) * FrozenMMap::<u8>::SLOT_SIZE
            );
        }

        #[test]
        fn ok_grow_sync_cycle() {
            let (_dir, cfg) = new_tmp();
            let mmap = FrozenMMap::<u8>::new(cfg).unwrap();

            for _ in 0..0x0A {
                mmap.grow(0x100).unwrap();
            }

            assert_eq!(
                mmap.core.curr_length(),
                (INIT_SLOTS + (0x0A * 0x100)) * FrozenMMap::<u8>::SLOT_SIZE
            );
        }

        #[test]
        fn ok_write_grow_read() {
            let (_dir, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(cfg).unwrap();

            mmap.write(0, |v| *v = 0xAA).unwrap();
            mmap.grow(0x10).unwrap();
            mmap.write(0, |v| *v = 0xBB).unwrap();

            let val = mmap.read(0, |v| *v).unwrap();
            assert_eq!(val, 0xBB);
        }

        #[test]
        fn ok_write_grow_read_cycle() {
            let (_dir, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(cfg).unwrap();
            mmap.write(0, |v| *v = 1).unwrap();

            for i in 0..5 {
                mmap.grow(0x10).unwrap();
                let idx = mmap.slots() - 1;
                mmap.write(idx, |v| *v = (i + 2) as u64).unwrap();
            }

            let base = mmap.read(0, |v| *v).unwrap();
            assert_eq!(base, 1);

            let last_idx = mmap.slots() - 1;
            let last = mmap.read(last_idx, |v| *v).unwrap();
            assert_eq!(last, 6);
        }
    }

    mod fm_write_read {
        use super::*;

        #[test]
        fn ok_write_wait_read_cycle() {
            const VAL: u32 = 0xDEADC0DE;
            let (_dir, cfg) = new_tmp();
            let mmap = FrozenMMap::<u32>::new(cfg).unwrap();

            // write + sync
            let (_, epoch) = mmap.write(0, |ptr| *ptr = VAL).unwrap();
            mmap.wait_for_durability(epoch).unwrap();

            // read + verify
            let val = mmap.read(0, |ptr| *ptr).unwrap();
            assert_eq!(val, VAL);
        }

        #[test]
        fn ok_write_read_without_wait() {
            const VAL: u32 = 0xDEADC0DE;
            let (_dir, cfg) = new_tmp();
            let mmap = FrozenMMap::<u32>::new(cfg).unwrap();

            mmap.write(0, |ptr| *ptr = VAL).unwrap();
            let val = mmap.read(0, |ptr| *ptr).unwrap();
            assert_eq!(val, VAL);
        }
    }

    mod fm_durability {
        use super::*;

        #[test]
        fn ok_wait_then_drop() {
            let (_dir, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(cfg).unwrap();

            let (_, epoch) = mmap.write(0, |v| *v = 7).unwrap();
            mmap.wait_for_durability(epoch).unwrap();

            drop(mmap);
        }

        #[test]
        fn ok_epoch_monotonicity() {
            let (_dir, cfg) = new_tmp();
            let mmap = FrozenMMap::<u64>::new(cfg).unwrap();

            let (_, e1) = mmap.write(0, |v| *v = 1).unwrap();
            mmap.wait_for_durability(e1).unwrap();

            let (_, e2) = mmap.write(0, |v| *v = 2).unwrap();
            mmap.wait_for_durability(e2).unwrap();
            assert!(e2 >= e1);
        }

        #[test]
        fn ok_wait_for_durability_with_multi_writers() {
            let (_dir, cfg) = new_tmp();
            let mmap = sync::Arc::new(FrozenMMap::<u64>::new(cfg).unwrap());

            let mut handles = Vec::new();
            for _ in 0..0x0A {
                let mmap = mmap.clone();
                handles.push(thread::spawn(move || {
                    let (_, epoch) = mmap.write(0, |v| *v += 1).unwrap();
                    mmap.wait_for_durability(epoch).unwrap();
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            let val = mmap.read(0, |v| *v).unwrap();
            assert_eq!(val, 0x0A);
        }
    }

    mod fm_concurrency {
        use super::*;

        #[test]
        fn ok_oi_lock_with_multi_threads_same_index() {
            let (_dir, cfg) = new_tmp();
            let mmap = sync::Arc::new(FrozenMMap::<u64>::new(cfg).unwrap());

            let mut handles = Vec::new();
            for _ in 0..0x0A {
                let mmap = mmap.clone();
                handles.push(thread::spawn(move || {
                    for _ in 0..0x100 {
                        mmap.write(0, |v| *v += 1).unwrap();
                    }
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            let val = mmap.read(0, |v| *v).unwrap();
            assert_eq!(val, 0x0A * 0x100);
        }

        #[test]
        fn ok_parallel_reads_with_diff_index() {
            let (_dir, cfg) = new_tmp();
            let mmap = sync::Arc::new(FrozenMMap::<u64>::new(cfg).unwrap());

            mmap.write(0, |v| *v = 0x10).unwrap();
            mmap.write(1, |v| *v = 0x20).unwrap();

            let t1 = {
                let mmap = mmap.clone();
                thread::spawn(move || mmap.read(0, |v| *v).unwrap())
            };

            let t2 = {
                let mmap = mmap.clone();
                thread::spawn(move || mmap.read(1, |v| *v).unwrap())
            };

            assert_eq!(t1.join().unwrap(), 0x10);
            assert_eq!(t2.join().unwrap(), 0x20);
        }

        #[test]
        fn ok_grow_with_multi_threads() {
            let (_dir, cfg) = new_tmp();
            let mmap = sync::Arc::new(FrozenMMap::<u64>::new(cfg).unwrap());

            const THREADS: usize = 4;
            const GROWS_PER_THREAD: usize = 0x10;

            let mut handles = Vec::new();
            for _ in 0..THREADS {
                let mmap = mmap.clone();
                handles.push(thread::spawn(move || {
                    for _ in 0..GROWS_PER_THREAD {
                        mmap.grow(1).unwrap();

                        // write to last slot after grow
                        let idx = mmap.slots() - 1;
                        mmap.write(idx, |v| *v = 0xABCD).unwrap();
                    }
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            let expected_min = INIT_SLOTS + (THREADS * GROWS_PER_THREAD);
            assert_eq!(mmap.slots(), expected_min);

            let last = mmap.read(mmap.slots() - 1, |v| *v).unwrap();
            assert_eq!(last, 0xABCD);
        }

        #[test]
        fn ok_wait_during_grow_cycle() {
            let (_dir, cfg) = new_tmp();

            let mmap = sync::Arc::new(FrozenMMap::<u64>::new(cfg).unwrap());
            let mmap2 = mmap.clone();

            let t = thread::spawn(move || {
                let (_, epoch) = mmap2.write(0, |v| *v = 42).unwrap();
                mmap2.wait_for_durability(epoch).unwrap();
            });

            mmap.grow(8).unwrap();
            t.join().unwrap();

            let val = mmap.read(0, |v| *v).unwrap();
            assert_eq!(val, 42);
        }
    }
}
