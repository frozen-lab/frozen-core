//! Custom implementation of `std::fs::File`
//!
//! ## Example
//!
//! ```
//! use frozen_core::ffile::{FrozenFile, FrozenFileCfg};
//!
//! const MID: u8 = 0;
//!
//! let dir = tempfile::tempdir().unwrap();
//! let path = dir.path().join("tmp_frozen_file");
//!
//! let cfg = FrozenFileCfg {
//!     module_id: MID,
//!     buffer_size: 0x10,
//!     path: path.to_path_buf(),
//!     initial_available_buffers: 0x0A,
//! };
//!
//! let file = FrozenFile::new(cfg.clone()).unwrap();
//! assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
//!
//! let mut data = vec![1u8; 0x10];
//! assert!(file.pwrite(data.as_mut_ptr(), 0).is_ok());
//! assert!(file.sync().is_ok());
//!
//! let mut buf = vec![0u8; data.len()];
//! assert!(file.pread(buf.as_mut_ptr(), 0).is_ok());
//! assert_eq!(buf, data);
//!
//! assert!(FrozenFile::new(cfg.clone()).is_err());
//!
//! assert!(file.delete().is_ok());
//! assert!(!path.exists());
//!
//! drop(file);
//! assert!(FrozenFile::new(cfg).is_ok());
//! ```

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::error::FrozenResult;

/// File descriptor of [`FrozenFile`]
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub type TFileId = libc::c_int;

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TFile = posix::POSIXFile;

/// Error codes for [`FrozenFile`]
pub(in crate::ffile) mod err {
    use crate::error::{ErrCode, FrozenError, FrozenResult};

    /// Domain Id for [`FrozenFile`] is **17**
    const ERRDOMAIN: u8 = 0x11;

    /// module id used for [`FrozenError`]
    pub static MID: std::sync::OnceLock<u8> = std::sync::OnceLock::new();

    #[cfg(not(test))]
    #[inline(always)]
    pub fn mid() -> &'static u8 {
        MID.get().unwrap()
    }

    #[cfg(test)]
    #[inline(always)]
    pub fn mid() -> &'static u8 {
        MID.get_or_init(|| 0)
    }

    /// internal fuck up (hault and catch fire)
    pub const HCF: ErrCode = ErrCode::new(0x02, "hault and catch fire");

    /// unknown error (fallback)
    pub const UNK: ErrCode = ErrCode::new(0x04, "unknown error");

    /// no more space available
    pub const NSP: ErrCode = ErrCode::new(0x08, "not enough space available on the storage device");

    /// syncing error
    pub const SYN: ErrCode = ErrCode::new(0x0A, "failed to sync/flush data to storage device");

    /// no write perm
    pub const WRT: ErrCode = ErrCode::new(0x0C, "missing permissions for write");

    /// no read perm
    pub const RED: ErrCode = ErrCode::new(0x0E, "missing permissions for read");

    /// invalid file path
    pub const INV: ErrCode = ErrCode::new(0x10, "invalid path to file");

    /// corrupted file
    pub const CPT: ErrCode = ErrCode::new(0x12, "file is either invalid or corrupted");

    /// unable to grow
    pub const GRW: ErrCode = ErrCode::new(0x14, "unable to zero-extend file");

    /// locks exhausted (mainly on nfs)
    pub const LEX: ErrCode =
        ErrCode::new(0x18, "failed to obtain lock, as no more locks available");

    /// no write/read perm
    pub const PRM: ErrCode = ErrCode::new(0x1A, "missing permissions for IO");

    /// unable to obtain exclusive lock
    pub const LCK: ErrCode =
        ErrCode::new(0x1C, "failed to obtain exclusive lock as file may already opened");

    #[inline]
    pub(in crate::ffile) fn new_err<R, E: std::fmt::Display>(
        code: ErrCode,
        error: E,
    ) -> FrozenResult<R> {
        let err = FrozenError::new_raw(*mid(), ERRDOMAIN, code, error);
        Err(err)
    }

    #[inline]
    pub(in crate::ffile) fn new_err_default<R>(code: ErrCode) -> FrozenResult<R> {
        let err = FrozenError::new(*mid(), ERRDOMAIN, code, "");
        Err(err)
    }
}

/// Config for [`FrozenFile`]
#[derive(Debug, Clone)]
pub struct FrozenFileCfg {
    /// Identifier used for error propagation by [`frozen_core::error::FrozenError`]
    pub module_id: u8,

    /// Absolute path for/of the file
    ///
    /// *NOTE:* The caller must make sure that the path represents a file and all the parent
    /// directories included in the path do exists.
    pub path: std::path::PathBuf,

    /// Size (in bytes) of a single chunk in file
    ///
    /// A chunk is a small fixed size allocation and addressing unit used by [`FrozenFile`] for all
    /// the write/read ops. These ops are operated by index of the chunk and not the offset of the
    /// byte.
    ///
    /// *NOTE:* Chunk size when power of 2, is cache efficient and good for performance
    pub buffer_size: usize,

    /// Number of chunks to pre-allocate on fs when [`FrozenFile`] is initialized
    ///
    /// Initial file length will be `buffer_size * initial_available_buffers` (bytes).
    pub initial_available_buffers: usize,
}

/// Custom implementation of `std::fs::File`
///
/// ## Example
///
/// ```
/// use frozen_core::ffile::{FrozenFile, FrozenFileCfg};
///
/// const MID: u8 = 0;
///
/// let dir = tempfile::tempdir().unwrap();
/// let path = dir.path().join("tmp_frozen_file");
///
/// let cfg = FrozenFileCfg {
///     module_id: MID,
///     buffer_size: 0x10,
///     path: path.to_path_buf(),
///     initial_available_buffers: 0x0A,
/// };
///
/// let file = FrozenFile::new(cfg.clone()).unwrap();
/// assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
///
/// let mut data = vec![1u8; 0x10];
/// assert!(file.pwrite(data.as_mut_ptr(), 0).is_ok());
/// assert!(file.sync().is_ok());
///
/// let mut buf = vec![0u8; data.len()];
/// assert!(file.pread(buf.as_mut_ptr(), 0).is_ok());
/// assert_eq!(buf, data);
///
/// assert!(FrozenFile::new(cfg.clone()).is_err());
///
/// assert!(file.delete().is_ok());
/// assert!(!path.exists());
///
/// drop(file);
/// assert!(FrozenFile::new(cfg).is_ok());
/// ```
#[derive(Debug)]
pub struct FrozenFile {
    cfg: FrozenFileCfg,
    file: core::cell::UnsafeCell<core::mem::ManuallyDrop<TFile>>,
}

unsafe impl Send for FrozenFile {}
unsafe impl Sync for FrozenFile {}

impl FrozenFile {
    /// Read current length of [`FrozenFile`]
    #[inline]
    pub fn length(&self) -> FrozenResult<usize> {
        unsafe { self.get_file().length() }
    }

    /// Get file descriptor for [`FrozenFile`]
    #[inline]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn fd(&self) -> TFileId {
        self.get_file().fd()
    }

    /// Check if the [`FrozenFile`] exists on the fs
    pub fn exists(&self) -> FrozenResult<bool> {
        unsafe { TFile::exists(&self.cfg.path) }
    }

    /// Create a new or open an existing [`FrozenFile`]
    ///
    /// ## [`FrozenFileCfg`]
    ///
    /// All configs for [`FrozenFile`] are stored in [`FrozenFileCfg`]
    ///
    /// ## Important
    ///
    /// The provided [`FrozenFileCfg`] must remain identical across all reopen cycles of the
    /// [`FrozenFile`].
    ///
    /// Changing any of the feilds after initial creation, may violate internal layout invariants
    /// and cause the file to be treated as corrupted.
    ///
    /// ## Multiple Instances
    ///
    /// Every instance of [`FrozenFile`] tries to acquire an exclusive lock, which protects against
    /// operating with multiple simultenious instances.
    ///
    /// If trying to call [`FrozenFile::new`] when already called, [`FFileErr::Lck`] error will be
    /// thrown.
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FrozenFileCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FrozenFileCfg {
    ///     module_id: MID,
    ///     buffer_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_available_buffers: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
    /// ```
    pub fn new(cfg: FrozenFileCfg) -> FrozenResult<Self> {
        let raw_file = unsafe { posix::POSIXFile::new(&cfg.path) }?;
        let slf = Self {
            cfg: cfg.clone(),
            file: core::cell::UnsafeCell::new(core::mem::ManuallyDrop::new(raw_file)),
        };

        let file = slf.get_file();

        // INFO: right after open is successful, we must obtain an exclusive lock on the entire file.
        // So the another instance of [`FrozenFile`] will try to access the same lock, would
        // correctly fail with [`FFileErr::Lck`] error.
        unsafe { file.flock() }?;

        // NOTE: The value is used for error logging and is initialized only once, as `OnceLock`
        // guarantees that the first caller sets the value and all subsequent calls reuse it
        let _ = err::MID.get_or_init(|| cfg.module_id);

        let curr_len = slf.length()?;
        let init_len = cfg.buffer_size * cfg.initial_available_buffers;

        match curr_len {
            0 => slf.grow(cfg.initial_available_buffers)?,
            _ => {
                // NOTE: we can treat these invariants as errors only because, our system guarantees,
                // whenever file size is updated, i.e. has grown, it'll always be a multiple of
                // `buffer_size`, and will have minimum of `buffer_size * initial_available_buffers`
                // (bytes) as it's length, although it only holds true when any of the params in
                // provided `cfg` are never updated after the initial creation of the file
                //
                // INFO: when true, we close the file to avoid resource leaks
                if (curr_len < init_len) || (curr_len % cfg.buffer_size != 0) {
                    // NOTE: we supress the close error as we are already in an errored state
                    let _ = unsafe { file.close() };
                    return err::new_err_default(err::CPT);
                }
            }
        }

        Ok(slf)
    }

    /// Syncs in-mem data on the storage device
    pub fn sync(&self) -> FrozenResult<()> {
        let file = self.get_file();
        unsafe { file.sync() }
    }

    /// A best-effort call to prompt kernel to start flushing dirty pages in the specified range
    ///
    /// This call, by itself, does not guarantee any kind of durability, and must always be paired
    /// with strong sync call i.e. [`FrozenFile::sync`]
    #[cfg(target_os = "linux")]
    pub fn sync_range(&self, index: usize, count: usize) -> FrozenResult<()> {
        let offset = self.cfg.buffer_size * index;
        let len_to_sync = self.cfg.buffer_size * count;
        let file = self.get_file();

        unsafe { file.sync_range(offset, len_to_sync) }
    }

    /// Delete [`FrozenFile`] from fs
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FrozenFileCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FrozenFileCfg {
    ///     module_id: MID,
    ///     buffer_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_available_buffers: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    /// assert!(file.exists().unwrap());
    ///
    /// file.delete().unwrap();
    /// assert!(!file.exists().unwrap());
    /// ```
    pub fn delete(&self) -> FrozenResult<()> {
        let file = self.get_file();
        unsafe { file.unlink(&self.cfg.path) }
    }

    /// Read a single chunk at given `index` w/ `pread` syscall
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FrozenFileCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FrozenFileCfg {
    ///     module_id: MID,
    ///     buffer_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_available_buffers: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    ///
    /// let mut data = [7u8; 0x10];
    /// file.pwrite(data.as_mut_ptr(), 2).unwrap();
    /// file.sync().unwrap();
    ///
    /// let mut buf = [0u8; 0x10];
    /// file.pread(buf.as_mut_ptr(), 2).unwrap();
    ///
    /// assert_eq!(buf, data);
    /// ```
    #[inline(always)]
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn pread(&self, buf: *mut u8, index: usize) -> FrozenResult<()> {
        let offset = self.cfg.buffer_size * index;
        let file = self.get_file();

        unsafe { file.pread(buf, offset, self.cfg.buffer_size) }
    }

    /// Write a single chunk at given `index` w/ `pwrite` syscall
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FrozenFileCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FrozenFileCfg {
    ///     module_id: MID,
    ///     buffer_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_available_buffers: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    ///
    /// let mut data = [9u8; 0x10];
    /// file.pwrite(data.as_mut_ptr(), 4).unwrap();
    /// file.sync().unwrap();
    ///
    /// let mut buf = [0u8; 0x10];
    /// file.pread(buf.as_mut_ptr(), 4).unwrap();
    ///
    /// assert_eq!(buf, data);
    /// ```
    #[inline(always)]
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn pwrite(&self, buf: *mut u8, index: usize) -> FrozenResult<()> {
        let offset = self.cfg.buffer_size * index;
        let file = self.get_file();

        unsafe { file.pwrite(buf, offset, self.cfg.buffer_size) }
    }

    /// Read multiple chunks starting from given `index` till `bufs.len()` w/ `preadv` syscall
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FrozenFileCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FrozenFileCfg {
    ///     module_id: MID,
    ///     buffer_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_available_buffers: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    ///
    /// let mut write_bufs = [[1u8; 0x10], [2u8; 0x10]];
    /// let ptrs: Vec<*mut u8> = write_bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();
    ///
    /// file.pwritev(&ptrs, 0).unwrap();
    /// file.sync().unwrap();
    ///
    /// let mut read_bufs = [[0u8; 0x10], [0u8; 0x10]];
    /// let rptrs: Vec<*mut u8> = read_bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();
    ///
    /// file.preadv(&rptrs, 0).unwrap();
    ///
    /// assert!(read_bufs[0].iter().all(|b| *b == 1));
    /// assert!(read_bufs[1].iter().all(|b| *b == 2));
    /// ```
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn preadv(&self, bufs: &[*mut u8], index: usize) -> FrozenResult<()> {
        let offset = self.cfg.buffer_size * index;
        let file = self.get_file();

        unsafe { file.preadv(bufs, offset, self.cfg.buffer_size) }
    }

    /// Write multiple chunks starting from given `index` till `bufs.len()` w/ `pwritev` syscall
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FrozenFileCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FrozenFileCfg {
    ///     module_id: MID,
    ///     buffer_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_available_buffers: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    ///
    /// let mut bufs = [[3u8; 0x10], [4u8; 0x10]];
    /// let ptrs: Vec<*mut u8> = bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();
    ///
    /// file.pwritev(&ptrs, 2).unwrap();
    /// file.sync().unwrap();
    ///
    /// let mut a = [0u8; 0x10];
    /// let mut b = [0u8; 0x10];
    ///
    /// file.pread(a.as_mut_ptr(), 2).unwrap();
    /// file.pread(b.as_mut_ptr(), 3).unwrap();
    ///
    /// assert!(a.iter().all(|v| *v == 3));
    /// assert!(b.iter().all(|v| *v == 4));
    /// ```
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn pwritev(&self, bufs: &[*mut u8], index: usize) -> FrozenResult<()> {
        let offset = self.cfg.buffer_size * index;
        let file = self.get_file();

        unsafe { file.pwritev(bufs, offset, self.cfg.buffer_size) }
    }

    /// Grow file size of [`FrozenFile`] by given `count` of chunks
    ///
    /// After successful execution, updated file length will be `current_length + (count * buffer_size)`
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FrozenFileCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FrozenFileCfg {
    ///     module_id: MID,
    ///     buffer_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_available_buffers: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
    ///
    /// file.grow(0x20).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x10 * (0x0A + 0x20));
    /// ```
    pub fn grow(&self, count: usize) -> FrozenResult<()> {
        let curr_len = self.length()?;
        let len_to_add = self.cfg.buffer_size * count;

        unsafe { self.get_file().grow(curr_len, len_to_add) }
    }

    /// Fetch total available chunks in [`FrozenFile`] from fs
    ///
    /// ## Working
    ///
    /// This call performs a syscall to fetch current length of [`FrozenFile`] from fs, as the
    /// current length of the file is not cached anywhere in the pipeline to avoid TOCTAU race
    /// conditions.
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FrozenFileCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FrozenFileCfg {
    ///     module_id: MID,
    ///     buffer_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_available_buffers: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
    ///
    /// file.grow(0x20).unwrap();
    /// assert_eq!(file.total_chunks().unwrap(), 0x0A + 0x20);
    /// ```
    #[inline]
    pub fn total_chunks(&self) -> FrozenResult<usize> {
        let curr_len = self.length()?;
        let buffer_size = self.cfg.buffer_size;

        if crate::hints::unlikely(curr_len % buffer_size != 0) {
            return err::new_err_default(err::CPT);
        }

        Ok(curr_len / buffer_size)
    }

    #[inline]
    fn get_file(&self) -> &core::mem::ManuallyDrop<TFile> {
        unsafe { &*self.file.get() }
    }
}

impl Drop for FrozenFile {
    fn drop(&mut self) {
        // guard for when delete is called (or drop on drop if its somehow possible)
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if self.fd() == posix::CLOSED_FD {
            return;
        }

        // sync if dirty & close
        let _ = self.sync();
        let _ = unsafe { self.get_file().close() };
    }
}

impl core::fmt::Display for FrozenFile {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "FrozenFile {{fd: {}, len: {}}}", self.fd(), self.length().unwrap_or(0),)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync;

    const MID: u8 = 0;
    const INIT_BUFFERS: usize = 4;
    const BUFFER_SIZE: usize = 0x10;

    fn tmp_path() -> (tempfile::TempDir, FrozenFileCfg) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tmp_ff_file");
        let cfg = FrozenFileCfg {
            path,
            module_id: MID,
            buffer_size: BUFFER_SIZE,
            initial_available_buffers: INIT_BUFFERS,
        };

        (dir, cfg)
    }

    mod ff_lifecycle {
        use super::*;

        #[test]
        fn ok_new_with_init_len() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            let exists = file.exists().unwrap();
            assert!(exists);

            assert_eq!(file.length().unwrap(), BUFFER_SIZE * INIT_BUFFERS);
        }

        #[test]
        fn ok_new_existing() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new(cfg.clone()).unwrap();
            assert_eq!(file.length().unwrap(), BUFFER_SIZE * INIT_BUFFERS);

            // must be dropped to release the exclusive lock
            drop(file);

            let reopened = FrozenFile::new(cfg.clone()).unwrap();
            assert_eq!(reopened.length().unwrap(), BUFFER_SIZE * INIT_BUFFERS);
        }

        #[test]
        fn err_new_when_file_smaller_than_init_len() {
            let (_dir, mut cfg) = tmp_path();

            let file = FrozenFile::new(cfg.clone()).unwrap();
            drop(file);

            // updated cfg
            cfg.buffer_size *= 2;

            let err = FrozenFile::new(cfg).unwrap_err();
            assert_eq!(err.reason, err::CPT.reason);
        }

        #[test]
        fn ok_exists_true_when_exists() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            let exists = file.exists().unwrap();
            assert!(exists);
        }

        #[test]
        fn ok_exists_false_when_missing() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();
            file.delete().unwrap();

            let exists = file.exists().unwrap();
            assert!(!exists);
        }

        #[test]
        fn ok_delete_file() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new(cfg).unwrap();
            let exists = file.exists().unwrap();
            assert!(exists);

            file.delete().unwrap();
            let exists = file.exists().unwrap();
            assert!(!exists);
        }

        #[test]
        fn err_delete_after_delete() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new(cfg).unwrap();
            file.delete().unwrap();

            let err = file.delete().unwrap_err();
            assert_eq!(err.reason, err::INV.reason);
        }

        #[test]
        fn ok_drop_persists_without_explicit_sync() {
            let mut data = [0x0Bu8; BUFFER_SIZE];
            let (_dir, cfg) = tmp_path();

            {
                let file = FrozenFile::new(cfg.clone()).unwrap();
                file.pwrite(data.as_mut_ptr(), 0).unwrap();
                drop(file);
            }

            {
                let reopened = FrozenFile::new(cfg).unwrap();
                let mut buf = [0u8; BUFFER_SIZE];

                reopened.pread(buf.as_mut_ptr(), 0).unwrap();
                assert_eq!(buf, data);
            }
        }
    }

    mod ff_lock {
        use super::*;

        #[test]
        fn err_new_when_already_open() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg.clone()).unwrap();

            let err = FrozenFile::new(cfg).unwrap_err();
            assert_eq!(err.reason, err::LCK.reason);

            drop(file);
        }

        #[test]
        fn ok_drop_releases_exclusive_lock() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new(cfg.clone()).unwrap();
            drop(file);

            let _ = FrozenFile::new(cfg).expect("must not fail after drop");
        }
    }

    mod ff_grow {
        use super::*;

        #[test]
        fn ok_grow_updates_length() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new(cfg).unwrap();
            assert_eq!(file.length().unwrap(), BUFFER_SIZE * INIT_BUFFERS);

            file.grow(0x20).unwrap();
            assert_eq!(file.length().unwrap(), BUFFER_SIZE * (INIT_BUFFERS + 0x20));
        }

        #[test]
        fn ok_grow_sync_cycle() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            for _ in 0..0x0A {
                file.grow(0x100).unwrap();
                file.sync().unwrap();
            }

            assert_eq!(file.length().unwrap(), BUFFER_SIZE * (INIT_BUFFERS + (0x0A * 0x100)));
        }
    }

    mod ff_sync {
        use super::*;

        #[test]
        fn ok_sync_after_sync() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            file.sync().unwrap();
            file.sync().unwrap();
            file.sync().unwrap();
        }

        #[test]
        fn err_sync_after_delete() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();
            file.delete().unwrap();

            let err = file.sync().unwrap_err();
            assert_eq!(err.reason, err::HCF.reason);
        }
    }

    mod ff_write_read {
        use super::*;

        #[test]
        fn ok_single_write_read_cycle() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            let mut data = [0x0Bu8; BUFFER_SIZE];

            file.pwrite(data.as_mut_ptr(), 4).unwrap();
            file.sync().unwrap();

            let mut buf = [0u8; BUFFER_SIZE];
            file.pread(buf.as_mut_ptr(), 4).unwrap();
            assert_eq!(buf, data);
        }

        #[test]
        fn ok_vectored_write_read_cycle() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            let mut bufs = [[1u8; BUFFER_SIZE], [2u8; BUFFER_SIZE]];
            let bufs: Vec<*mut u8> = bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();

            file.pwritev(&bufs, 0).unwrap();
            file.sync().unwrap();

            let mut read_bufs = [[0u8; BUFFER_SIZE], [0u8; BUFFER_SIZE]];
            let rbufs: Vec<*mut u8> = read_bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();
            file.preadv(&rbufs, 0).unwrap();

            assert!(read_bufs[0].iter().all(|b| *b == 1));
            assert!(read_bufs[1].iter().all(|b| *b == 2));
        }

        #[test]
        fn ok_write_concurrent_non_overlapping() {
            let (_dir, mut cfg) = tmp_path();
            cfg.initial_available_buffers = 0x100;
            let file = sync::Arc::new(FrozenFile::new(cfg).unwrap());

            let mut handles = vec![];
            for i in 0..2 {
                let f = file.clone();
                handles.push(std::thread::spawn(move || {
                    let mut data = [i as u8; BUFFER_SIZE];
                    f.pwrite(data.as_mut_ptr(), i).unwrap();
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            file.sync().unwrap();

            for i in 0..2 {
                let mut buf = [0u8; BUFFER_SIZE];
                file.pread(buf.as_mut_ptr(), i).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn ok_concurrent_grow_and_write() {
            let (_dir, cfg) = tmp_path();
            let file = sync::Arc::new(FrozenFile::new(cfg).unwrap());

            let writer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for i in 0..INIT_BUFFERS {
                        let mut data = [i as u8; BUFFER_SIZE];
                        f.pwrite(data.as_mut_ptr(), i).unwrap();
                    }
                })
            };

            let chunks_to_grow = 0x20;
            let grower = {
                let f = file.clone();
                std::thread::spawn(move || {
                    f.grow(chunks_to_grow).unwrap();
                })
            };

            writer.join().unwrap();
            grower.join().unwrap();

            file.sync().unwrap();
            assert_eq!(file.length().unwrap(), BUFFER_SIZE * (INIT_BUFFERS + chunks_to_grow));

            for i in 0..INIT_BUFFERS {
                let mut buf = [0u8; BUFFER_SIZE];
                file.pread(buf.as_mut_ptr(), i).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn ok_concurrent_sync_and_write() {
            let (_dir, cfg) = tmp_path();
            let file = sync::Arc::new(FrozenFile::new(cfg).unwrap());

            let writer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for i in 0..INIT_BUFFERS {
                        let mut data = [i as u8; BUFFER_SIZE];
                        f.pwrite(data.as_mut_ptr(), i).unwrap();
                    }
                })
            };

            let syncer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for _ in 0..2 {
                        f.sync().unwrap();
                    }
                })
            };

            writer.join().unwrap();
            syncer.join().unwrap();

            file.sync().unwrap();

            for i in 0..INIT_BUFFERS {
                let mut buf = [0; BUFFER_SIZE];
                file.pread(buf.as_mut_ptr(), i).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn err_read_hcf_for_eof() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            // index > curr_chunks
            let mut buf = [0; BUFFER_SIZE];
            let err = file.pread(buf.as_mut_ptr(), 0x100).unwrap_err();
            assert_eq!(err.reason, err::HCF.reason);
        }
    }
}
