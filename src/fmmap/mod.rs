//! Custom implementation of `memmap`

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::{
    error::{FrozenErr, FrozenRes},
    ffile::FrozenFile,
    hints,
};
use alloc::{sync, vec::Vec};
use core::{cell, fmt, mem, sync::atomic, time};

/// Domain Id for [`FrozenMMap`] is **18**
const ERRDOMAIN: u8 = 0x12;

/// default auto flush state for [`FMCfg`]
const AUTO_FLUSH: bool = false;

/// default flush duration for [`FMCfg`]
const FLUSH_DURATION: time::Duration = time::Duration::from_millis(250);

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TMap = posix::POSIXMMap;

/// module id used for [`FrozenErr`]
static MID: atomic::AtomicU8 = atomic::AtomicU8::new(0);

#[inline]
pub(in crate::fmmap) fn mid() -> u8 {
    MID.load(atomic::Ordering::Relaxed)
}

/// Error codes for [`FrozenFile`]
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
    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, message);
    Err(err)
}

/// Config for [`FrozenMMap`]
#[derive(Clone)]
pub struct FMCfg {
    /// module id for [`FrozenMMap`]
    ///
    /// This id is used for error codes
    ///
    /// ## Why
    ///
    /// It enables for easier identification of error boundries when multiple [`FrozenMMap`]
    /// modules are present in the codebase
    pub module_id: u8,

    /// when true, all dirty pages would be synced by background thread
    pub auto_flush: bool,

    /// time interval for sync to flush dirty pages
    pub flush_duration: time::Duration,
}

impl FMCfg {
    /// Create a new instance of [`FMCfg`] w/ specified `module_id`
    pub const fn new(module_id: u8) -> Self {
        Self {
            module_id,
            auto_flush: AUTO_FLUSH,
            flush_duration: FLUSH_DURATION,
        }
    }

    /// Enable `auto_flush` for intervaled background sync for [`FrozenMMap`]
    pub const fn enable_auto_flush(mut self) -> Self {
        self.auto_flush = true;
        self
    }

    /// Set the interval for sync in [`FrozenMMap`]
    pub const fn flush_duration(mut self, interval: time::Duration) -> Self {
        self.flush_duration = interval;
        self
    }
}

/// Custom implementation of MemMap
pub struct FrozenMMap(sync::Arc<Core>);

unsafe impl Send for FrozenMMap {}
unsafe impl Sync for FrozenMMap {}

impl FrozenMMap {
    /// Read current length of [`FrozenMMap`]
    #[inline]
    pub fn length(&self) -> usize {
        self.0.length
    }

    /// Create a new [`FrozenMMap`] for given `fd` w/ read & write permissions
    pub fn new(file: FrozenFile, length: usize, cfg: FMCfg) -> FrozenRes<Self> {
        let mmap = unsafe { posix::POSIXMMap::new(file.fd(), length) }?;
        let core = sync::Arc::new(Core::new(mmap, cfg.clone(), length, file));

        Ok(Self(core))
    }

    /// Syncs in-mem data on the storage device
    ///
    /// ## `F_FULLFSYNC` vs `msync`
    ///
    /// On mac (the supposed best os),`msync()` does not guarantee that the dirty pages are flushed
    /// by the storage device, and it may not physically write the data to the platters for
    /// quite some time
    ///
    /// More info [here](https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/msync.2.html)
    ///
    /// To achieve true crash durability (including protection against power loss),
    /// we must use `fcntl(fd, F_FULLFSYNC)` which provides strict durability guarantees
    ///
    /// If `F_FULLFSYNC` is not supported by the underlying filesystem or device
    /// (e.g., returns `EINVAL`, `ENOTSUP`, or `EOPNOTSUPP`), we fall back to
    /// `fsync()` as a best-effort persistence mechanism
    #[inline]
    pub fn sync(&self) -> FrozenRes<()> {
        let closed = self.0.dropped.load(atomic::Ordering::Acquire);
        if hints::unlikely(closed) {
            return new_err(FMMapErrRes::Hcf, b"Trying to access closed FrozenMMap".to_vec());
        }

        self.0.sync()
    }

    /// Get a [`FMReader`] object for `T` at given `offset`
    ///
    /// **NOTE**: `offset` must be 8 bytes aligned
    #[inline]
    pub fn reader<'a, T>(&'a self, offset: usize) -> FrozenRes<FMReader<'a, T>> {
        let reader = FMReader {
            ptr: unsafe { self.get_mmap().get(offset) },
            _guard: ActiveGuard { core: &self.0 },
        };

        Ok(reader)
    }

    /// Get a [`FMWriter`] object for `T` at given `offset`
    ///
    /// **NOTE**: `offset` must be 8 bytes aligned
    #[inline]
    pub fn writer<'a, T>(&'a self, offset: usize) -> FrozenRes<FMWriter<'a, T>> {
        let writer = FMWriter {
            map: self,
            ptr: unsafe { self.get_mmap().get_mut(offset) },
            _guard: ActiveGuard { core: &self.0 },
        };

        Ok(writer)
    }

    #[inline]
    fn munmap(&self) -> FrozenRes<()> {
        unsafe { self.get_mmap().unmap(self.length(), self.0.cfg.module_id) }
    }

    #[inline]
    fn get_mmap(&self) -> &mem::ManuallyDrop<TMap> {
        unsafe { &*self.0.mmap.get() }
    }
}

impl Drop for FrozenMMap {
    fn drop(&mut self) {
        if self.0.dropped.swap(true, atomic::Ordering::AcqRel) {
            return;
        }

        // sync if dirty
        if self.0.dirty.swap(false, atomic::Ordering::AcqRel) {
            let _ = self.sync();
        }

        let _ = self.munmap();
    }
}

impl fmt::Display for FrozenMMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FrozenMMap{{len: {}, id: {}, mode: {}}}",
            self.length(),
            self.0.cfg.module_id,
            self.0.cfg.auto_flush,
        )
    }
}

struct Core {
    cfg: FMCfg,
    length: usize,
    ffile: FrozenFile,
    dirty: atomic::AtomicBool,
    dropped: atomic::AtomicBool,
    active: atomic::AtomicUsize,
    mmap: cell::UnsafeCell<mem::ManuallyDrop<TMap>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(mmap: TMap, cfg: FMCfg, length: usize, ffile: FrozenFile) -> Self {
        Self {
            cfg,
            ffile,
            length,
            active: atomic::AtomicUsize::new(0),
            dirty: atomic::AtomicBool::new(false),
            dropped: atomic::AtomicBool::new(false),
            mmap: cell::UnsafeCell::new(mem::ManuallyDrop::new(mmap)),
        }
    }

    #[inline]
    fn sync(&self) -> FrozenRes<()> {
        unsafe {
            let mmap = &*self.mmap.get();

            #[cfg(target_os = "linux")]
            return mmap.sync(self.length, self.cfg.module_id);

            #[cfg(target_os = "macos")]
            return self.ffile.sync();
        }
    }
}

struct ActiveGuard<'a> {
    core: &'a Core,
}

impl Drop for ActiveGuard<'_> {
    fn drop(&mut self) {
        if self.core.active.fetch_sub(1, atomic::Ordering::Release) == 1 {
            // last user
            // if let Ok(_g) = self.core.lock.lock() {
            //     self.core.shutdown_cv.notify_one();
            // }
        }
    }
}

/// Reader object for [`FrozenMMap`]
pub struct FMReader<'a, T> {
    ptr: *const T,
    _guard: ActiveGuard<'a>,
}

impl<'a, T> FMReader<'a, T> {
    /// Get's an immutable (read only) typed pointer for `T`
    #[inline]
    pub fn read<R>(&self, f: impl FnOnce(&T) -> R) -> R {
        unsafe { f(&*self.ptr) }
    }
}

/// Writer object for [`FrozenMMap`]
pub struct FMWriter<'a, T> {
    ptr: *mut T,
    map: &'a FrozenMMap,
    _guard: ActiveGuard<'a>,
}

impl<'a, T> FMWriter<'a, T> {
    /// Get's a mutable (read & write) typed pointer for `T`
    #[inline]
    pub fn write<R>(&self, f: impl FnOnce(&mut T) -> R) -> FrozenRes<R> {
        let res = unsafe { f(&mut *self.ptr) };
        match self.map.0.cfg.auto_flush {
            false => self.map.sync()?,
            true => {
                self.map.0.dirty.store(true, atomic::Ordering::Release);
                // self.map.0.cv.notify_one();
            }
        }
        Ok(res)
    }
}
