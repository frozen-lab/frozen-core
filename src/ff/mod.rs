//! Custom implementation of `std::fs::File`

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::fe::{FErr, FRes};
use std::{
    cell, fmt, mem, path,
    sync::{self, atomic},
};

/// Domain Id for [`FrozenFile`] is **17**
const ERRDOMAIN: u8 = 0x11;

#[cfg(any(target_os = "linux", target_os = "macos"))]
type FFile = posix::POSIXFile;

/// Error codes for [`FrozenFile`]
#[repr(u16)]
pub enum FFErr {
    /// (256) internal fuck up
    Hcf = 0x100,

    /// (257) unknown error (fallback)
    Unk = 0x101,

    /// (258) no more space available
    Nsp = 0x102,

    /// (259) syncing error
    Syn = 0x103,

    /// (260) no write perm
    Wrt = 0x104,

    /// (261) no read perm
    Red = 0x105,

    /// (262) invalid path
    Inv = 0x106,
}

#[inline]
pub(in crate::ff) fn new_error<E, R>(mid: u8, reason: FFErr, error: E) -> FRes<R>
where
    E: fmt::Display,
{
    let code = crate::fe::new_err_code(mid, ERRDOMAIN, reason as u16);
    let err = FErr::with_err(code, error);
    Err(err)
}

/// Config for [`FrozenFile`]
#[derive(Clone)]
pub struct FFCfg {
    /// module id for [`FrozenFile`]
    ///
    /// This id is used for error codes
    ///
    /// ## Why
    ///
    /// It enables for easier identification of error boundries when multiple [`FM`]
    /// modules are present in the codebase
    pub module_id: u8,

    /// Path of the file
    pub path: path::PathBuf,
}

impl FFCfg {
    /// Create a new instance of [`FFCfg`] w/ specified `module_id`
    pub const fn new(path: path::PathBuf, module_id: u8) -> Self {
        Self { path, module_id }
    }
}

/// Custom implementation of File
pub struct FrozenFile(sync::Arc<Core>);

unsafe impl Send for FrozenFile {}
unsafe impl Sync for FrozenFile {}

impl FrozenFile {
    /// Read current length of [`FrozenFile`]
    #[inline]
    pub fn length(&self) -> u64 {
        self.0.length.load(atomic::Ordering::Acquire)
    }

    /// Get file descriptor for [`FrozenFile`]
    #[inline]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn fd(&self) -> i32 {
        self.get_file().fd()
    }

    /// Create new [`FrozenFile`] w/ specified length
    pub fn new(cfg: FFCfg, length: u64) -> FRes<Self> {
        let file = unsafe { posix::POSIXFile::new(&cfg.path, cfg.module_id) }?;
        let core = sync::Arc::new(Core::new(file, cfg.clone(), length));

        let ff = Self(core.clone());
        if let Err(e) = ff.grow(length) {
            // NOTE: we delete the file so new init could work w/o any errors
            // HACK: we ignore the delete error, cause we already in errored state
            let _ = ff.delete();
            return Err(e);
        }

        Ok(ff)
    }

    /// Open an existing [`FrozenFile`]
    pub fn open(cfg: FFCfg) -> FRes<Self> {
        let file = unsafe { posix::POSIXFile::open(&cfg.path, cfg.module_id) }?;
        let length = unsafe { file.length(cfg.module_id) }?;
        let core = sync::Arc::new(Core::new(file, cfg.clone(), length));
        Ok(Self(core.clone()))
    }

    /// Grow [`FrozenFile`] w/ given `len_to_add`
    #[inline(always)]
    pub fn grow(&self, len_to_add: u64) -> FRes<()> {
        unsafe { self.get_file().grow(self.length(), len_to_add, self.0.cfg.module_id) }.inspect(|_| {
            let _ = self.0.length.fetch_add(len_to_add, atomic::Ordering::Release);
        })
    }

    /// Syncs in-mem data on the storage device
    #[inline]
    pub fn sync(&self) -> FRes<()> {
        self.0.sync()
    }

    /// Delete [`FrozenFile`] from filesystem
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn delete(&self) -> FRes<()> {
        let file = self.get_file();

        // NOTE: sanity check is invalid here, cause we are deleting the file, hence we don't
        // actually care if the state is sane or not ;)

        unsafe { file.unlink(&self.0.cfg.path, self.0.cfg.module_id) }
    }

    #[inline]
    fn get_file(&self) -> &mem::ManuallyDrop<FFile> {
        unsafe { &*self.0.file.get() }
    }
}

impl Drop for FrozenFile {
    fn drop(&mut self) {
        // sync if dirty & close
        let _ = self.0.sync();
        let _ = unsafe { self.get_file().close(self.0.cfg.module_id) };
    }
}

impl fmt::Display for FrozenFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FrozenFile {{fd: {}, len: {}, id: {}}}",
            self.fd(),
            self.length(),
            self.0.cfg.module_id,
        )
    }
}

struct Core {
    cfg: FFCfg,
    length: atomic::AtomicU64,
    file: cell::UnsafeCell<mem::ManuallyDrop<FFile>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(file: FFile, cfg: FFCfg, length: u64) -> Self {
        Self {
            cfg,
            length: atomic::AtomicU64::new(length),
            file: cell::UnsafeCell::new(mem::ManuallyDrop::new(file)),
        }
    }

    #[inline]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn sync(&self) -> FRes<()> {
        unsafe { (&*self.file.get()).sync(self.cfg.module_id) }
    }
}
