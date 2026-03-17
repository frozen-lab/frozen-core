//! Custom implementation of `std::fs::File`
//!
//! ## Example
//!
//! ```
//! use frozen_core::ffile::{FrozenFile, FFCfg};
//!
//! const MID: u8 = 0;
//!
//! let dir = tempfile::tempdir().unwrap();
//! let path = dir.path().join("tmp_frozen_file");
//!
//! let cfg = FFCfg {
//!     chunk_size: 0x10,
//!     path: path.to_path_buf(),
//!     initial_chunk_amount: 0x0A,
//! };
//!
//! let file = FrozenFile::new::<MID>(cfg.clone()).unwrap();
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
//! assert!(FrozenFile::new::<MID>(cfg.clone()).is_err());
//!
//! assert!(file.delete().is_ok());
//! assert!(!path.exists());
//!
//! drop(file);
//! assert!(FrozenFile::new::<MID>(cfg).is_ok());
//! ```

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::error::{ErrCode, FrozenErr, FrozenRes};

/// Domain Id for [`FrozenFile`] is **17**
const ERRDOMAIN: u8 = 0x11;

/// File descriptor for [`FrozenFile`]
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub type TFileId = libc::c_int;

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TFile = posix::POSIXFile;

/// module id used for [`FrozenErr`]
static MID: std::sync::OnceLock<u8> = std::sync::OnceLock::new();

#[cfg(not(test))]
#[inline(always)]
fn mid() -> &'static u8 {
    MID.get().unwrap()
}

#[cfg(test)]
#[inline(always)]
fn mid() -> &'static u8 {
    MID.get_or_init(|| 0)
}

/// Error codes for [`FrozenFile`]
pub(in crate::ffile) mod err {
    use super::ErrCode;

    /// (256) internal fuck up (hault and catch fire)
    pub const HCF: ErrCode = ErrCode::new(0x100, "hault and catch fire");

    /// (257) unknown error (fallback)
    pub const UNK: ErrCode = ErrCode::new(0x101, "unknown error");

    /// (258) no more space available
    pub const NSP: ErrCode = ErrCode::new(0x102, "not enough space available on the storage device");

    /// (259) syncing error
    pub const SYN: ErrCode = ErrCode::new(0x103, "failed to sync/flush data to storage device");

    /// (260) no write perm
    pub const WRT: ErrCode = ErrCode::new(0x104, "missing permissions for write");

    /// (261) no read perm
    pub const RED: ErrCode = ErrCode::new(0x105, "missing permissions for read");

    /// (262) invalid file path
    pub const INV: ErrCode = ErrCode::new(0x106, "invalid path to file");

    /// (263) corrupted file
    pub const CPT: ErrCode = ErrCode::new(0x107, "file is either invalid or corrupted");

    /// (264) unable to grow
    pub const GRW: ErrCode = ErrCode::new(0x108, "unable to zero-extend file");

    /// (265) unable to obtain exclusive lock
    pub const LCK: ErrCode = ErrCode::new(0x109, "failed to obtain exclusive lock as file may already opened");

    /// (266) locks exhausted (mainly on nfs)
    pub const LEX: ErrCode = ErrCode::new(0x10A, "failed to obtain lock, as no more locks available");

    /// (267) no write/read perm
    pub const PRM: ErrCode = ErrCode::new(0x10B, "missing permissions for IO");
}

#[inline]
pub(in crate::ffile) fn new_err<R, E: std::fmt::Display>(code: ErrCode, error: E) -> FrozenRes<R> {
    let err = FrozenErr::new_raw(*mid(), ERRDOMAIN, code, error);
    Err(err)
}

#[inline]
pub(in crate::ffile) fn new_err_default<R>(code: ErrCode) -> FrozenRes<R> {
    let err = FrozenErr::new(*mid(), ERRDOMAIN, code, "");
    Err(err)
}

/// Config for [`FrozenFile`]
#[derive(Debug, Clone)]
pub struct FFCfg {
    /// Path for the file
    ///
    /// *NOTE:* The caller must make sure that the parent directory exists
    pub path: std::path::PathBuf,

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
}

/// Custom implementation of `std::fs::File`
///
/// ## Example
///
/// ```
/// use frozen_core::ffile::{FrozenFile, FFCfg};
///
/// const MID: u8 = 0;
///
/// let dir = tempfile::tempdir().unwrap();
/// let path = dir.path().join("tmp_frozen_file");
///
/// let cfg = FFCfg {
///     chunk_size: 0x10,
///     path: path.to_path_buf(),
///     initial_chunk_amount: 0x0A,
/// };
///
/// let file = FrozenFile::new::<MID>(cfg.clone()).unwrap();
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
/// assert!(FrozenFile::new::<MID>(cfg.clone()).is_err());
///
/// assert!(file.delete().is_ok());
/// assert!(!path.exists());
///
/// drop(file);
/// assert!(FrozenFile::new::<MID>(cfg).is_ok());
/// ```
#[derive(Debug)]
pub struct FrozenFile {
    cfg: FFCfg,
    file: core::cell::UnsafeCell<core::mem::ManuallyDrop<TFile>>,
}

unsafe impl Send for FrozenFile {}
unsafe impl Sync for FrozenFile {}

impl FrozenFile {
    /// Read current length of [`FrozenFile`]
    #[inline]
    pub fn length(&self) -> FrozenRes<usize> {
        unsafe { self.get_file().length() }
    }

    /// Get file descriptor for [`FrozenFile`]
    #[inline]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn fd(&self) -> i32 {
        self.get_file().fd()
    }

    /// Check if [`FrozenFile`] exists on the fs
    pub fn exists(&self) -> FrozenRes<bool> {
        unsafe { TFile::exists(&self.cfg.path) }
    }

    /// Create a new or open an existing [`FrozenFile`]
    ///
    /// ## [`FFCfg`]
    ///
    /// All configs for [`FrozenFile`] are stored in [`FFCfg`]
    ///
    /// ## Important
    ///
    /// The `cfg` must not change any of its properties for the entire life of [`FrozenFile`],
    /// one must use config stores like [`Rta`](https://crates.io/crates/rta) to store config
    ///
    /// ## Multiple Instances
    ///
    /// We acquire an exclusive lock for the entire file, this protects against operating with
    /// multiple simultenious instance of [`FrozenFile`], when trying to call [`FrozenFile::new`]
    /// when already called, [`FFileErr::Lck`] error will be thrown
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FFCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FFCfg {
    ///     chunk_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_chunk_amount: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new::<MID>(cfg).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
    /// ```
    pub fn new<const MODULE_ID: u8>(cfg: FFCfg) -> FrozenRes<Self> {
        let raw_file = unsafe { posix::POSIXFile::new(&cfg.path) }?;
        let slf = Self {
            cfg: cfg.clone(),
            file: core::cell::UnsafeCell::new(core::mem::ManuallyDrop::new(raw_file)),
        };

        let file = slf.get_file();

        // INFO: right after open is successful, we must obtain an exclusive lock on the entire file, hence when
        // another instance of [`FrozenFile`], when trying to access the same file, would correctly fail, while
        // again obtaining the lock
        unsafe { file.flock() }?;

        // NOTE: The value is used for error logging and is initialized only once, as `OnceLock` guarantees that the
        // first caller sets the value and all subsequent calls reuse it
        let _ = MID.get_or_init(|| MODULE_ID);

        let curr_len = slf.length()?;
        let init_len = cfg.chunk_size * cfg.initial_chunk_amount;

        match curr_len {
            0 => slf.grow(cfg.initial_chunk_amount)?,
            _ => {
                // NOTE: we can treat this invariants as errors only because, our system guarantees,
                // whenever file size is updated, i.e. has grown, it'll always be a multiple of `chunk_size`,
                // and will have minimum of `chunk_size * initial_chunk_amount` (bytes) as the length, although
                // it only holds true when any of params in `cfg` are never updated after the file is created
                if (curr_len < init_len) || (curr_len % cfg.chunk_size != 0) {
                    // INFO:
                    // - close the file to avoid resource leaks
                    // - we supress the close error, as we are already in an errored state
                    let _ = unsafe { file.close() };
                    return new_err_default(err::CPT);
                }
            }
        }

        Ok(slf)
    }

    /// Syncs in-mem data on the storage device
    pub fn sync(&self) -> FrozenRes<()> {
        let file = self.get_file();
        unsafe { file.sync() }
    }

    /// Initiates writeback (best-effort) of dirty pages in the specified range
    #[cfg(target_os = "linux")]
    pub fn sync_range(&self, index: usize, count: usize) -> FrozenRes<()> {
        let offset = self.cfg.chunk_size * index;
        let len_to_sync = self.cfg.chunk_size * count;
        let file = self.get_file();

        unsafe { file.sync_range(offset, len_to_sync) }
    }

    /// Delete [`FrozenFile`] from fs
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FFCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FFCfg {
    ///     chunk_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_chunk_amount: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new::<MID>(cfg).unwrap();
    /// assert!(file.exists().unwrap());
    ///
    /// file.delete().unwrap();
    /// assert!(!file.exists().unwrap());
    /// ```
    pub fn delete(&self) -> FrozenRes<()> {
        let file = self.get_file();
        unsafe { file.unlink(&self.cfg.path) }
    }

    /// Read a single chunk at given `index` w/ `pread` syscall
    #[inline(always)]
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn pread(&self, buf: *mut u8, index: usize) -> FrozenRes<()> {
        let offset = self.cfg.chunk_size * index;
        let file = self.get_file();

        unsafe { file.pread(buf, offset, self.cfg.chunk_size) }
    }

    /// Write a single chunk at given `index` w/ `pwrite` syscall
    #[inline(always)]
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn pwrite(&self, buf: *mut u8, index: usize) -> FrozenRes<()> {
        let offset = self.cfg.chunk_size * index;
        let file = self.get_file();

        unsafe { file.pwrite(buf, offset, self.cfg.chunk_size) }
    }

    /// Read multiple chunks starting from given `index` till `bufs.len()` w/ `preadv` syscall
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn preadv(&self, bufs: &[*mut u8], index: usize) -> FrozenRes<()> {
        let offset = self.cfg.chunk_size * index;
        let file = self.get_file();

        unsafe { file.preadv(bufs, offset, self.cfg.chunk_size) }
    }

    /// Write multiple chunks starting from given `index` till `bufs.len()` w/ `pwritev` syscall
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn pwritev(&self, bufs: &[*mut u8], index: usize) -> FrozenRes<()> {
        let offset = self.cfg.chunk_size * index;
        let file = self.get_file();

        unsafe { file.pwritev(bufs, offset, self.cfg.chunk_size) }
    }

    /// Grow file size of [`FrozenFile`] by given `count` of chunks
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FFCfg};
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FFCfg {
    ///     chunk_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_chunk_amount: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new::<MID>(cfg).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
    ///
    /// file.grow(0x20).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x10 * (0x0A + 0x20));
    /// ```    
    pub fn grow(&self, count: usize) -> FrozenRes<()> {
        let curr_len = self.length()?;
        let len_to_add = self.cfg.chunk_size * count;

        unsafe { self.get_file().grow(curr_len, len_to_add) }
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
        write!(
            f,
            "FrozenFile {{fd: {}, len: {}}}",
            self.fd(),
            self.length().unwrap_or(0),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    const CHUNK_SIZE: usize = 0x10;
    const INIT_CHUNKS: usize = 0x0A;
    const MID: u8 = 0;

    fn tmp_path() -> (tempfile::TempDir, FFCfg) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tmp_ff_file");
        let cfg = FFCfg {
            path,
            chunk_size: CHUNK_SIZE,
            initial_chunk_amount: INIT_CHUNKS,
        };

        (dir, cfg)
    }

    mod ff_lifecycle {
        use super::*;

        #[test]
        fn ok_new_with_init_len() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new::<MID>(cfg).unwrap();

            let exists = file.exists().unwrap();
            assert!(exists);

            assert_eq!(file.length().unwrap(), CHUNK_SIZE * INIT_CHUNKS);
        }

        #[test]
        fn ok_new_existing() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new::<MID>(cfg.clone()).unwrap();
            assert_eq!(file.length().unwrap(), CHUNK_SIZE * INIT_CHUNKS);

            // must be dropped to release the exclusive lock
            drop(file);

            let reopened = FrozenFile::new::<MID>(cfg.clone()).unwrap();
            assert_eq!(reopened.length().unwrap(), CHUNK_SIZE * INIT_CHUNKS);
        }

        #[test]
        fn err_new_when_file_smaller_than_init_len() {
            let (_dir, mut cfg) = tmp_path();

            let file = FrozenFile::new::<MID>(cfg.clone()).unwrap();
            drop(file);

            // updated cfg
            cfg.chunk_size *= 2;

            let err = FrozenFile::new::<MID>(cfg).unwrap_err();
            assert_eq!((err.id & 0xffff) as u16, err::CPT.reason);
        }

        #[test]
        fn ok_exists_true_when_exists() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new::<MID>(cfg).unwrap();

            let exists = file.exists().unwrap();
            assert!(exists);
        }

        #[test]
        fn ok_exists_false_when_missing() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new::<MID>(cfg).unwrap();
            file.delete().unwrap();

            let exists = file.exists().unwrap();
            assert!(!exists);
        }

        #[test]
        fn ok_delete_file() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new::<MID>(cfg).unwrap();
            let exists = file.exists().unwrap();
            assert!(exists);

            file.delete().unwrap();
            let exists = file.exists().unwrap();
            assert!(!exists);
        }

        #[test]
        fn err_delete_after_delete() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new::<MID>(cfg).unwrap();
            file.delete().unwrap();

            let err = file.delete().unwrap_err();
            assert_eq!((err.id & 0xffff) as u16, err::INV.reason);
        }

        #[test]
        fn ok_drop_persists_without_explicit_sync() {
            let mut data = [0x0Bu8; CHUNK_SIZE];
            let (_dir, cfg) = tmp_path();

            {
                let file = FrozenFile::new::<MID>(cfg.clone()).unwrap();
                file.pwrite(data.as_mut_ptr(), 0).unwrap();
                drop(file);
            }

            {
                let reopened = FrozenFile::new::<MID>(cfg).unwrap();
                let mut buf = [0u8; CHUNK_SIZE];

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
            let file = FrozenFile::new::<MID>(cfg.clone()).unwrap();

            let err = FrozenFile::new::<MID>(cfg).unwrap_err();
            assert_eq!((err.id & 0xffff) as u16, err::LCK.reason);

            drop(file);
        }

        #[test]
        fn ok_drop_releases_exclusive_lock() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new::<MID>(cfg.clone()).unwrap();
            drop(file);

            let _ = FrozenFile::new::<MID>(cfg).expect("must not fail after drop");
        }
    }

    mod ff_grow {
        use super::*;

        #[test]
        fn ok_grow_updates_length() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new::<MID>(cfg).unwrap();
            assert_eq!(file.length().unwrap(), CHUNK_SIZE * INIT_CHUNKS);

            file.grow(0x20).unwrap();
            assert_eq!(file.length().unwrap(), CHUNK_SIZE * (INIT_CHUNKS + 0x20));
        }

        #[test]
        fn ok_grow_sync_cycle() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new::<MID>(cfg).unwrap();

            for _ in 0..0x0A {
                file.grow(0x100).unwrap();
                file.sync().unwrap();
            }

            assert_eq!(file.length().unwrap(), CHUNK_SIZE * (INIT_CHUNKS + (0x0A * 0x100)));
        }
    }

    mod ff_sync {
        use super::*;

        #[test]
        fn ok_sync_after_sync() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new::<MID>(cfg).unwrap();

            file.sync().unwrap();
            file.sync().unwrap();
            file.sync().unwrap();
        }

        #[test]
        fn err_sync_after_delete() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new::<MID>(cfg).unwrap();
            file.delete().unwrap();

            let err = file.sync().unwrap_err();
            assert_eq!((err.id & 0xffff) as u16, err::HCF.reason);
        }
    }

    mod ff_write_read {
        use super::*;

        #[test]
        fn ok_single_write_read_cycle() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new::<MID>(cfg).unwrap();

            let mut data = [0x0Bu8; CHUNK_SIZE];

            file.pwrite(data.as_mut_ptr(), 4).unwrap();
            file.sync().unwrap();

            let mut buf = [0u8; CHUNK_SIZE];
            file.pread(buf.as_mut_ptr(), 4).unwrap();
            assert_eq!(buf, data);
        }

        #[test]
        fn ok_vectored_write_read_cycle() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new::<MID>(cfg).unwrap();

            let mut bufs = [[1u8; CHUNK_SIZE], [2u8; CHUNK_SIZE]];
            let bufs: Vec<*mut u8> = bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();

            file.pwritev(&bufs, 0).unwrap();
            file.sync().unwrap();

            let mut read_bufs = [[0u8; CHUNK_SIZE], [0u8; CHUNK_SIZE]];
            let rbufs: Vec<*mut u8> = read_bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();
            file.preadv(&rbufs, 0).unwrap();

            assert!(read_bufs[0].iter().all(|b| *b == 1));
            assert!(read_bufs[1].iter().all(|b| *b == 2));
        }

        #[test]
        fn ok_write_concurrent_non_overlapping() {
            let (_dir, mut cfg) = tmp_path();
            cfg.initial_chunk_amount = 0x100;
            let file = Arc::new(FrozenFile::new::<MID>(cfg).unwrap());

            let mut handles = vec![];
            for i in 0..0x0A {
                let f = file.clone();
                handles.push(std::thread::spawn(move || {
                    let mut data = [i as u8; CHUNK_SIZE];
                    f.pwrite(data.as_mut_ptr(), i).unwrap();
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            file.sync().unwrap();

            for i in 0..0x0A {
                let mut buf = [0u8; CHUNK_SIZE];
                file.pread(buf.as_mut_ptr(), i).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn ok_concurrent_grow_and_write() {
            let (_dir, cfg) = tmp_path();
            let file = Arc::new(FrozenFile::new::<MID>(cfg).unwrap());

            let writer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for i in 0..INIT_CHUNKS {
                        let mut data = [i as u8; CHUNK_SIZE];
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
            assert_eq!(file.length().unwrap(), CHUNK_SIZE * (INIT_CHUNKS + chunks_to_grow));

            for i in 0..INIT_CHUNKS {
                let mut buf = [0u8; CHUNK_SIZE];
                file.pread(buf.as_mut_ptr(), i).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn ok_concurrent_sync_and_write() {
            let (_dir, cfg) = tmp_path();
            let file = Arc::new(FrozenFile::new::<MID>(cfg).unwrap());

            let writer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for i in 0..INIT_CHUNKS {
                        let mut data = [i as u8; CHUNK_SIZE];
                        f.pwrite(data.as_mut_ptr(), i).unwrap();
                    }
                })
            };

            let syncer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for _ in 0..0x0A {
                        f.sync().unwrap();
                    }
                })
            };

            writer.join().unwrap();
            syncer.join().unwrap();

            file.sync().unwrap();

            for i in 0..INIT_CHUNKS {
                let mut buf = [0; CHUNK_SIZE];
                file.pread(buf.as_mut_ptr(), i).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn err_read_hcf_for_eof() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new::<MID>(cfg).unwrap();

            // index > curr_chunks
            let mut buf = [0; CHUNK_SIZE];
            let err = file.pread(buf.as_mut_ptr(), 0x100).unwrap_err();
            assert_eq!((err.id & 0xffff) as u16, err::HCF.reason);
        }
    }
}
