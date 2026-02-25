//! Custom implementation of `std::fs::File`
//!
//! ## Example
//!
//! ```
//! use frozen_core::ffile::{FrozenFile, FFCfg};
//!
//! let dir = tempfile::tempdir().unwrap();
//! let path = dir.path().join("tmp_frozen_file");
//!
//! let cfg = FFCfg {
//!     mid: 0x00,
//!     chunk_size: 0x10,
//!     path: path.to_path_buf(),
//!     initial_chunk_amount: 0x0A,
//! };
//!
//! let file = FrozenFile::new(cfg.clone()).unwrap();
//! assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
//!
//! let data = vec![1u8; 0x10];
//! let iov = libc::iovec {
//!     iov_base: data.as_ptr() as *mut _,
//!     iov_len: data.len(),
//! };
//!
//! assert!(file.write(&iov, 0).is_ok());
//! assert!(file.sync().is_ok());
//!
//! let mut buf = vec![0u8; data.len()];
//! let mut read_iov = libc::iovec {
//!     iov_base: buf.as_mut_ptr() as *mut _,
//!     iov_len: buf.len(),
//! };
//!
//! assert!(file.read(&mut read_iov, 0).is_ok());
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

use crate::error::{FrozenErr, FrozenRes};
use core::{self, sync::atomic};

/// file descriptor for [`FrozenFile`]
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub type FFId = libc::c_int;

#[cfg(any(target_os = "linux", target_os = "macos"))]
type TFile = posix::POSIXFile;

/// Domain Id for [`FrozenFile`] is **17**
const ERRDOMAIN: u8 = 0x11;

/// module id used for [`FrozenErr`]
static MID: atomic::AtomicU8 = atomic::AtomicU8::new(0);

#[inline]
pub(in crate::ffile) fn mid() -> u8 {
    MID.load(atomic::Ordering::Relaxed)
}

/// Error codes for [`FrozenFile`]
#[repr(u16)]
pub enum FFileErrRes {
    /// (256) internal fuck up (hault and catch fire)
    Hcf = 0x100,

    /// (257) unknown error (fallback)
    Unk = 0x101,

    /// (258) no more space available
    Nsp = 0x102,

    /// (259) syncing error
    Syn = 0x103,

    /// (260) no write/read perm
    Prm = 0x104,

    /// (261) invalid path
    Inv = 0x105,

    /// (262) corrupted file
    Cpt = 0x106,

    /// (265) unable to grow
    Grw = 0x107,

    /// (266) unable to lock
    Lck = 0x108,

    /// (267) locks exhausted (mainly on nfs)
    Lex = 0x109,
}

impl FFileErrRes {
    #[inline]
    fn default_message(&self) -> &'static [u8] {
        match self {
            Self::Inv => b"invalid file path",
            Self::Unk => b"unknown error type",
            Self::Hcf => b"hault and catch fire",
            Self::Grw => b"unable to grow the file",
            Self::Prm => b"missing write/read permissions",
            Self::Nsp => b"no space left on storage device",
            Self::Cpt => b"file is either invalid or corrupted",
            Self::Syn => b"failed to sync/flush data to storage device",
            Self::Lex => b"failed to obtain lock, as no more locks available",
            Self::Lck => b"failed to obtain exclusive lock, file may already be open",
        }
    }
}

#[inline]
pub(in crate::ffile) fn new_err<R>(res: FFileErrRes, message: Vec<u8>) -> FrozenRes<R> {
    let detail = res.default_message();
    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, message);
    Err(err)
}

#[inline]
pub(in crate::ffile) fn new_err_default<R>(res: FFileErrRes) -> FrozenRes<R> {
    let detail = res.default_message();
    let err = FrozenErr::new(mid(), ERRDOMAIN, res as u16, detail, Vec::with_capacity(0));
    Err(err)
}

/// Config for [`FrozenFile`]
#[derive(Debug, Clone)]
pub struct FFCfg {
    /// Module id used for error logging
    pub mid: u8,

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
/// let dir = tempfile::tempdir().unwrap();
/// let path = dir.path().join("tmp_frozen_file");
///
/// let cfg = FFCfg {
///     mid: 0x00,
///     chunk_size: 0x10,
///     path: path.to_path_buf(),
///     initial_chunk_amount: 0x0A,
/// };
///
/// let file = FrozenFile::new(cfg.clone()).unwrap();
/// assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
///
/// let data = vec![1u8; 0x10];
/// let iov = libc::iovec {
///     iov_base: data.as_ptr() as *mut _,
///     iov_len: data.len(),
/// };
///
/// assert!(file.write(&iov, 0).is_ok());
/// assert!(file.sync().is_ok());
///
/// let mut buf = vec![0u8; data.len()];
/// let mut read_iov = libc::iovec {
///     iov_base: buf.as_mut_ptr() as *mut _,
///     iov_len: buf.len(),
/// };
///
/// assert!(file.read(&mut read_iov, 0).is_ok());
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

    /// check if [`FrozenFile`] exists on the fs
    pub fn exists(&self) -> FrozenRes<bool> {
        unsafe { TFile::exists(&self.cfg.path) }
    }

    /// create a new or open an existing [`FrozenFile`]
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
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FFCfg};
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FFCfg {
    ///     mid: 0x00,
    ///     chunk_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_chunk_amount: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
    ///```
    pub fn new(cfg: FFCfg) -> FrozenRes<Self> {
        let raw_file = unsafe { posix::POSIXFile::new(&cfg.path) }?;
        let slf = Self {
            cfg: cfg.clone(),
            file: core::cell::UnsafeCell::new(core::mem::ManuallyDrop::new(raw_file)),
        };

        let file = slf.get_file();

        // INFO: right after open is successful, we must obtain an exclusive lock on the
        // entire file, hence when another instance of [`FrozenFile`], when trying to access
        // the same file, would correctly fail, while again obtaining the lock
        unsafe { file.flock() }?;

        // NOTE: we only set it once, as once after an exclusive lock for the entire file is
        // acquired, hence it'll be only set once per instance and is only used for error logging
        MID.store(cfg.mid, atomic::Ordering::Relaxed);

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
                    return new_err_default(FFileErrRes::Cpt);
                }
            }
        }

        Ok(slf)
    }

    /// Grow file size of [`FrozenFile`] by given `count` of chunks
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FFCfg};
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FFCfg {
    ///     mid: 0x00,
    ///     chunk_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_chunk_amount: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
    ///
    /// file.grow(0x20).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x10 * (0x0A + 0x20));
    ///```    
    pub fn grow(&self, count: usize) -> FrozenRes<()> {
        let curr_len = self.length()?;
        let len_to_add = self.cfg.chunk_size * count;

        unsafe { self.get_file().grow(curr_len, len_to_add) }
    }

    /// Syncs in-mem data on the storage device
    pub fn sync(&self) -> FrozenRes<()> {
        let file = self.get_file();
        unsafe { file.sync() }
    }

    /// Initiates writeback (best-effort) of dirty pages in the specified range
    #[cfg(any(target_os = "linux"))]
    pub fn sync_range(&self, index: usize, count: usize) -> FrozenRes<()> {
        let offset = self.cfg.chunk_size * index;
        let len_to_sync = self.cfg.chunk_size * count;
        let file = self.get_file();

        unsafe { file.sync_range(offset, len_to_sync) }
    }

    /// Delete [`FrozenFile`] from filesystem
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::{FrozenFile, FFCfg};
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let cfg = FFCfg {
    ///     mid: 0x00,
    ///     chunk_size: 0x10,
    ///     path: path.to_path_buf(),
    ///     initial_chunk_amount: 0x0A,
    /// };
    ///
    /// let file = FrozenFile::new(cfg).unwrap();
    /// assert!(file.exists().unwrap());
    ///
    /// file.delete().unwrap();
    /// assert!(!file.exists().unwrap());
    ///```
    pub fn delete(&self) -> FrozenRes<()> {
        let file = self.get_file();
        unsafe { file.unlink(&self.cfg.path) }
    }

    /// Read a single `iovec` chunk at given `index` w/ `pread` syscall
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn read(&self, buf: &mut libc::iovec, index: usize) -> FrozenRes<()> {
        // sanity check
        debug_assert_eq!(buf.iov_len, self.cfg.chunk_size);

        let offset = self.cfg.chunk_size * index;
        let file = self.get_file();

        unsafe { file.pread(buf, offset) }
    }

    /// Write a single `iovec` chunk at given `index` w/ `pwrite` syscall
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn write(&self, buf: &libc::iovec, index: usize) -> FrozenRes<()> {
        // sanity check
        debug_assert_eq!(buf.iov_len, self.cfg.chunk_size);

        let offset = self.cfg.chunk_size * index;
        let file = self.get_file();

        unsafe { file.pwrite(buf, offset) }
    }

    /// Read multiple `iovec` chunks starting from given `index` till `iovs.len()` w/ `preadv` syscall
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn preadv(&self, iovs: &mut [libc::iovec], index: usize) -> FrozenRes<()> {
        // sanity check
        debug_assert!(iovs.iter().all(|i| i.iov_len == self.cfg.chunk_size));

        let offset = self.cfg.chunk_size * index;
        let file = self.get_file();

        unsafe { file.preadv(iovs, offset) }
    }

    /// Write multiple `iovec` chunks starting from given `index` till `iovs.len()` w/ `pwritev` syscall
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn pwritev(&self, iovs: &mut [libc::iovec], index: usize) -> FrozenRes<()> {
        // sanity check
        debug_assert!(iovs.iter().all(|i| i.iov_len == self.cfg.chunk_size));

        let offset = self.cfg.chunk_size * index;
        let file = self.get_file();

        unsafe { file.pwritev(iovs, offset) }
    }

    #[inline]
    fn get_file(&self) -> &core::mem::ManuallyDrop<TFile> {
        unsafe { &*self.file.get() }
    }
}

impl Drop for FrozenFile {
    fn drop(&mut self) {
        // TODO: try not to consume errors here, fail is required to tackle to
        // when explicit drop is called

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
    use crate::error::TEST_MID;
    use std::sync::Arc;

    const CHUNK_SIZE: usize = 0x10;
    const INIT_CHUNKS: usize = 0x0A;

    fn tmp_path() -> (tempfile::TempDir, FFCfg) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tmp_ff_file");
        let cfg = FFCfg {
            path: path,
            mid: TEST_MID,
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
            let file = FrozenFile::new(cfg).unwrap();

            let exists = file.exists().unwrap();
            assert!(exists);

            assert_eq!(file.length().unwrap(), CHUNK_SIZE * INIT_CHUNKS);
        }

        #[test]
        fn ok_new_existing() {
            let (_dir, cfg) = tmp_path();

            let file = FrozenFile::new(cfg.clone()).unwrap();
            assert_eq!(file.length().unwrap(), CHUNK_SIZE * INIT_CHUNKS);

            // must be dropped to release the exclusive lock
            drop(file);

            let reopened = FrozenFile::new(cfg.clone()).unwrap();
            assert_eq!(reopened.length().unwrap(), CHUNK_SIZE * INIT_CHUNKS);
        }

        #[test]
        fn err_new_when_file_smaller_than_init_len() {
            let (_dir, mut cfg) = tmp_path();

            let file = FrozenFile::new(cfg.clone()).unwrap();
            drop(file);

            // updated cfg
            cfg.chunk_size = cfg.chunk_size * 2;

            let err = FrozenFile::new(cfg).unwrap_err();
            assert!(err.cmp(FFileErrRes::Cpt as u16));
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
            assert!(err.cmp(FFileErrRes::Inv as u16));
        }

        #[test]
        fn ok_drop_persists_without_explicit_sync() {
            let data = [0x0Bu8; CHUNK_SIZE];
            let (_dir, cfg) = tmp_path();

            {
                let file = FrozenFile::new(cfg.clone()).unwrap();
                let iov = libc::iovec {
                    iov_base: data.as_ptr() as *mut _,
                    iov_len: data.len(),
                };
                file.write(&iov, 0).unwrap();
                drop(file);
            }

            {
                let reopened = FrozenFile::new(cfg).unwrap();
                let mut buf = [0u8; CHUNK_SIZE];
                let mut iov = libc::iovec {
                    iov_base: buf.as_mut_ptr() as *mut _,
                    iov_len: buf.len(),
                };

                reopened.read(&mut iov, 0).unwrap();
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
            assert!(err.cmp(FFileErrRes::Lck as u16));

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
            assert_eq!(file.length().unwrap(), CHUNK_SIZE * INIT_CHUNKS);

            file.grow(0x20).unwrap();
            assert_eq!(file.length().unwrap(), CHUNK_SIZE * (INIT_CHUNKS + 0x20));
        }

        #[test]
        fn ok_grow_sync_cycle() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            for _ in 0..0x0A {
                file.grow(0x100).unwrap();
                file.sync().unwrap();
            }
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
            assert!(err.cmp(FFileErrRes::Hcf as u16));
        }
    }

    mod ff_write_read {
        use super::*;

        #[test]
        fn ok_single_write_read_cycle() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            let data = [0x0Bu8; CHUNK_SIZE];
            let iov = libc::iovec {
                iov_base: data.as_ptr() as *mut _,
                iov_len: data.len(),
            };

            file.write(&iov, 4).unwrap();
            file.sync().unwrap();

            let mut buf = [0u8; CHUNK_SIZE];
            let mut read_iov = libc::iovec {
                iov_base: buf.as_mut_ptr() as *mut _,
                iov_len: buf.len(),
            };

            file.read(&mut read_iov, 4).unwrap();
            assert_eq!(buf, data);
        }

        #[test]
        fn ok_vectored_write_read_cycle() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            let mut bufs = [[1u8; CHUNK_SIZE], [2u8; CHUNK_SIZE]];
            let mut iovs: Vec<libc::iovec> = bufs
                .iter_mut()
                .map(|b| libc::iovec {
                    iov_base: b.as_mut_ptr() as *mut _,
                    iov_len: b.len(),
                })
                .collect();

            file.pwritev(&mut iovs, 0).unwrap();
            file.sync().unwrap();

            let mut read_bufs = [[0u8; CHUNK_SIZE], [0u8; CHUNK_SIZE]];
            let mut read_iovs: Vec<libc::iovec> = read_bufs
                .iter_mut()
                .map(|b| libc::iovec {
                    iov_base: b.as_mut_ptr() as *mut _,
                    iov_len: b.len(),
                })
                .collect();

            file.preadv(&mut read_iovs, 0).unwrap();
            assert!(read_bufs[0].iter().all(|b| *b == 1));
            assert!(read_bufs[1].iter().all(|b| *b == 2));
        }

        #[test]
        fn ok_write_concurrent_non_overlapping() {
            let (_dir, mut cfg) = tmp_path();
            cfg.initial_chunk_amount = 0x100;
            let file = Arc::new(FrozenFile::new(cfg).unwrap());

            let mut handles = vec![];
            for i in 0..0x0A {
                let f = file.clone();
                handles.push(std::thread::spawn(move || {
                    let data = [i as u8; CHUNK_SIZE];
                    let iov = libc::iovec {
                        iov_base: data.as_ptr() as *mut _,
                        iov_len: data.len(),
                    };

                    f.write(&iov, i).unwrap();
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            file.sync().unwrap();

            for i in 0..0x0A {
                let mut buf = [0u8; CHUNK_SIZE];
                let mut iov = libc::iovec {
                    iov_base: buf.as_mut_ptr() as *mut _,
                    iov_len: buf.len(),
                };

                file.read(&mut iov, i).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn ok_concurrent_grow_and_write() {
            let (_dir, cfg) = tmp_path();
            let file = Arc::new(FrozenFile::new(cfg).unwrap());

            let writer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for i in 0..INIT_CHUNKS {
                        let data = [i as u8; CHUNK_SIZE];
                        let iov = libc::iovec {
                            iov_base: data.as_ptr() as *mut _,
                            iov_len: data.len(),
                        };

                        f.write(&iov, i).unwrap();
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
                let mut iov = libc::iovec {
                    iov_base: buf.as_mut_ptr() as *mut _,
                    iov_len: buf.len(),
                };

                file.read(&mut iov, i).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn ok_concurrent_sync_and_write() {
            let (_dir, cfg) = tmp_path();
            let file = Arc::new(FrozenFile::new(cfg).unwrap());

            let writer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for i in 0..INIT_CHUNKS {
                        let data = [i as u8; CHUNK_SIZE];
                        let iov = libc::iovec {
                            iov_base: data.as_ptr() as *mut _,
                            iov_len: data.len(),
                        };

                        f.write(&iov, i).unwrap();
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
                let mut iov = libc::iovec {
                    iov_base: buf.as_mut_ptr() as *mut _,
                    iov_len: buf.len(),
                };

                file.read(&mut iov, i).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn err_read_hcf_for_eof() {
            let (_dir, cfg) = tmp_path();
            let file = FrozenFile::new(cfg).unwrap();

            let mut buf = [0; CHUNK_SIZE];
            let mut iov = libc::iovec {
                iov_base: buf.as_mut_ptr() as *mut _,
                iov_len: buf.len(),
            };

            // index > curr_chunks
            let err = file.read(&mut iov, 0x100).unwrap_err();
            assert!(err.cmp(FFileErrRes::Hcf as u16));
        }
    }
}
