//! Custom implementation of `std::fs::File`
//!
//! ## Example
//!
//! ```
//! use frozen_core::ffile::FrozenFile;
//!
//! const MID: u8 = 0;
//!
//! let dir = tempfile::tempdir().unwrap();
//! let path = dir.path().join("tmp_frozen_file");
//! let file = FrozenFile::new(&path, 0x1000, MID).unwrap();
//!
//! let data = b"hello grave";
//! let iov = libc::iovec {
//!     iov_base: data.as_ptr() as *mut _,
//!     iov_len: data.len(),
//! };
//!
//! assert!(file.write(&iov, 0x80).is_ok());
//! assert!(file.sync().is_ok());
//!
//! let mut buf = vec![0u8; data.len()];
//! let mut read_iov = libc::iovec {
//!     iov_base: buf.as_mut_ptr() as *mut _,
//!     iov_len: buf.len(),
//! };
//!
//! assert!(file.read(&mut read_iov, 0x80).is_ok());
//! assert_eq!(&buf, data);
//!
//! assert!(FrozenFile::new(&path, 0x1000, MID).is_err());
//!
//! assert!(file.delete().is_ok());
//! assert!(!path.exists());
//!
//! drop(file);
//! assert!(FrozenFile::new(&path, 0x1000, MID).is_ok());
//! ```

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod posix;

use crate::error::{FrozenErr, FrozenRes};
use core::{self, sync::atomic};
use std::sync::Arc;

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
/// use frozen_core::ffile::FrozenFile;
///
/// const MID: u8 = 0;
///
/// let dir = tempfile::tempdir().unwrap();
/// let path = dir.path().join("tmp_frozen_file");
/// let file = FrozenFile::new(&path, 0x1000, MID).unwrap();
///
/// let data = b"hello grave";
/// let iov = libc::iovec {
///     iov_base: data.as_ptr() as *mut _,
///     iov_len: data.len(),
/// };
///
/// assert!(file.write(&iov, 0x80).is_ok());
/// assert!(file.sync().is_ok());
///
/// let mut buf = vec![0u8; data.len()];
/// let mut read_iov = libc::iovec {
///     iov_base: buf.as_mut_ptr() as *mut _,
///     iov_len: buf.len(),
/// };
///
/// assert!(file.read(&mut read_iov, 0x80).is_ok());
/// assert_eq!(&buf, data);
///
/// assert!(FrozenFile::new(&path, 0x1000, MID).is_err());
///
/// assert!(file.delete().is_ok());
/// assert!(!path.exists());
///
/// drop(file);
/// assert!(FrozenFile::new(&path, 0x1000, MID).is_ok());
/// ```
#[derive(Debug)]
pub struct FrozenFile(Arc<Core>);

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
    pub fn exists(path: &std::path::Path) -> FrozenRes<bool> {
        unsafe { TFile::exists(path) }
    }

    /// create a new or open an existing [`FrozenFile`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::FrozenFile;
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let file = FrozenFile::new(&path, 0x1000, MID).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x1000);
    ///```
    pub fn new(path: &std::path::Path, init_len: usize, mid: u8) -> FrozenRes<Self> {
        MID.store(mid, atomic::Ordering::Relaxed); // used for err logging

        let file = unsafe { posix::POSIXFile::new(&path) }?;

        // INFO: right after open is successful, we must obtain an exclusive lock on the
        // entire file, hence when another instance of [`FrozenFile`], when trying to access
        // the same file, would correctly fail, while again obtaining the lock
        Self::request_exclusive_lock(&file)?;

        let curr_len = unsafe { file.length()? };
        match curr_len {
            0 => unsafe {
                file.grow(0, init_len)?;
            },
            _ => {
                if curr_len < init_len {
                    // close the file to avoid resource leaks
                    let _ = unsafe { file.close() };
                    return new_err_default(FFileErrRes::Cpt);
                }
            }
        }

        let core = Arc::new(Core::new(file, path));
        Ok(Self(core))
    }

    /// Grow [`FrozenFile`] w/ given `len_to_add`
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::FrozenFile;
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let file = FrozenFile::new(&path, 0x1000, MID).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x1000);
    ///
    /// file.grow(0x1000).unwrap();
    /// assert_eq!(file.length().unwrap(), 0x2000);
    ///```
    pub fn grow(&self, len_to_add: usize) -> FrozenRes<()> {
        unsafe {
            let curr_len = self.length()?;
            self.get_file().grow(curr_len, len_to_add)
        }
    }

    /// Syncs in-mem data on the storage device
    pub fn sync(&self) -> FrozenRes<()> {
        self.0.sync()
    }

    /// Initiates writeback (best-effort) of dirty pages in the specified range
    #[cfg(any(target_os = "linux"))]
    pub fn sync_range(&self, offset: usize, len: usize) -> FrozenRes<()> {
        self.0.sync_range(offset, len)
    }

    /// Delete [`FrozenFile`] from filesystem
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::ffile::FrozenFile;
    ///
    /// const MID: u8 = 0;
    ///
    /// let dir = tempfile::tempdir().unwrap();
    /// let path = dir.path().join("tmp_frozen_file");
    ///
    /// let file = FrozenFile::new(&path, 0x1000, MID).unwrap();
    /// assert!(path.exists());
    ///
    /// file.delete().unwrap();
    /// assert!(!path.exists());
    ///```
    pub fn delete(&self) -> FrozenRes<()> {
        let file = self.get_file();

        // NOTE: sanity check is invalid here, cause we are deleting the file, hence we don't
        // actually care if the state is sane or not ;)

        unsafe { file.unlink(&self.0.path) }
    }

    /// Read a single `iovec` from a given `offset` w/ `pread` syscall
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn read(&self, buf: &mut libc::iovec, offset: usize) -> FrozenRes<()> {
        unsafe { self.get_file().pread(buf, offset) }
    }

    /// Write a single `iovec` at a given `offset` w/ `pwrite` syscall
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn write(&self, buf: &libc::iovec, offset: usize) -> FrozenRes<()> {
        unsafe { self.get_file().pwrite(buf, offset) }
    }

    /// Read multiple `iovec` objects starting from given `offset` w/ `preadv` syscall
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn preadv(&self, iovs: &mut [libc::iovec], offset: usize) -> FrozenRes<()> {
        unsafe { self.get_file().preadv(iovs, offset) }
    }

    /// Write multiple `iovec` objects starting from given `offset` w/ `pwritev` syscall
    #[inline(always)]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn pwritev(&self, iovs: &mut [libc::iovec], offset: usize) -> FrozenRes<()> {
        unsafe { self.get_file().pwritev(iovs, offset) }
    }

    fn request_exclusive_lock(file: &TFile) -> FrozenRes<()> {
        unsafe { file.flock() }
    }

    #[inline]
    fn get_file(&self) -> &core::mem::ManuallyDrop<TFile> {
        unsafe { &*self.0.file.get() }
    }
}

impl Drop for FrozenFile {
    fn drop(&mut self) {
        // TODO: try not to consume errors here, fail is required to tackle to
        // when explicit drop is called

        // sync if dirty & close
        let _ = self.0.sync();
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

#[derive(Debug)]
struct Core {
    path: std::path::PathBuf,
    file: core::cell::UnsafeCell<core::mem::ManuallyDrop<TFile>>,
}

unsafe impl Send for Core {}
unsafe impl Sync for Core {}

impl Core {
    fn new(file: TFile, path: &std::path::Path) -> Self {
        Self {
            path: path.to_path_buf(),
            file: core::cell::UnsafeCell::new(core::mem::ManuallyDrop::new(file)),
        }
    }

    #[inline]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn sync(&self) -> FrozenRes<()> {
        unsafe { (&*self.file.get()).sync() }
    }

    #[inline]
    #[cfg(any(target_os = "linux"))]
    fn sync_range(&self, offset: usize, len: usize) -> FrozenRes<()> {
        unsafe { (&*self.file.get()).sync_range(offset, len) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::TEST_MID;
    use std::path::PathBuf;

    fn tmp_path() -> (tempfile::TempDir, PathBuf) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tmp_frozen_file");

        (dir, path)
    }

    mod ff_lifecycle {
        use super::*;

        #[test]
        fn ok_new_with_init_len() {
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x1000, TEST_MID).unwrap();

            assert!(path.exists());
            assert_eq!(file.length().unwrap(), 0x1000);
        }

        #[test]
        fn ok_new_existing() {
            let (_dir, path) = tmp_path();

            let file = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();
            assert_eq!(file.length().unwrap(), 0x200);

            // must be dropped to release the exclusive lock
            drop(file);

            let reopened = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();
            assert_eq!(reopened.length().unwrap(), 0x200);
        }

        #[test]
        fn err_new_when_file_smaller_than_init_len() {
            let (_dir, path) = tmp_path();

            let file = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();
            assert_eq!(file.length().unwrap(), 0x200);

            drop(file);

            let err = FrozenFile::new(&path, 0x400, TEST_MID).unwrap_err();
            assert!(err.cmp(FFileErrRes::Cpt as u16));
        }

        #[test]
        fn ok_exists_true_when_exists() {
            let (_dir, path) = tmp_path();
            let _ = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();

            let exists = FrozenFile::exists(&path).unwrap();
            assert!(exists);
        }

        #[test]
        fn ok_exists_false_when_missing() {
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();
            file.delete().unwrap();

            let exists = FrozenFile::exists(&path).unwrap();
            assert!(!exists);
        }

        #[test]
        fn ok_delete_file() {
            let (_dir, path) = tmp_path();

            let file = FrozenFile::new(&path, 0x100, TEST_MID).unwrap();
            assert!(path.exists());

            file.delete().unwrap();
            assert!(!path.exists());
        }

        #[test]
        fn err_delete_after_delete() {
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x100, TEST_MID).unwrap();

            file.delete().unwrap();

            let err = file.delete().unwrap_err();
            assert!(err.cmp(FFileErrRes::Inv as u16));
        }

        #[test]
        fn ok_drop_persists_without_explicit_sync() {
            let (_dir, path) = tmp_path();

            {
                let file = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();
                let data = b"persist";
                let iov = libc::iovec {
                    iov_base: data.as_ptr() as *mut _,
                    iov_len: data.len(),
                };
                file.write(&iov, 0).unwrap();
                drop(file);
            }

            {
                let reopened = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();
                let mut buf = vec![0u8; 7];
                let mut iov = libc::iovec {
                    iov_base: buf.as_mut_ptr() as *mut _,
                    iov_len: buf.len(),
                };

                reopened.read(&mut iov, 0).unwrap();
                assert_eq!(&buf, b"persist");
            }
        }
    }

    mod ff_lock {
        use super::*;

        #[test]
        fn err_new_when_already_open() {
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();

            let err = FrozenFile::new(&path, 0x200, TEST_MID).unwrap_err();
            assert!(err.cmp(FFileErrRes::Lck as u16));

            drop(file);
        }

        #[test]
        fn ok_drop_releases_exclusive_lock() {
            let (_dir, path) = tmp_path();

            let file = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();
            assert_eq!(file.length().unwrap(), 0x200);
            drop(file);

            let reopened = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();
            assert_eq!(reopened.length().unwrap(), 0x200);
        }
    }

    mod ff_grow {
        use super::*;

        #[test]
        fn ok_grow_updates_length() {
            let (_dir, path) = tmp_path();

            let file = FrozenFile::new(&path, 0x100, TEST_MID).unwrap();
            assert_eq!(file.length().unwrap(), 0x100);

            file.grow(0x100).unwrap();
            assert_eq!(file.length().unwrap(), 0x200);
        }

        #[test]
        fn ok_grow_sync_cycle() {
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x100, TEST_MID).unwrap();

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
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x100, TEST_MID).unwrap();

            file.sync().unwrap();
            file.sync().unwrap();
            file.sync().unwrap();
        }

        #[test]
        fn err_sync_after_delete() {
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x100, TEST_MID).unwrap();
            file.delete().unwrap();

            let err = file.sync().unwrap_err();
            assert!(err.cmp(FFileErrRes::Hcf as u16));
        }
    }

    mod ff_write_read {
        use super::*;

        #[test]
        fn ok_single_write_read_cycle() {
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x400, TEST_MID).unwrap();

            let data = b"grave";
            let iov = libc::iovec {
                iov_base: data.as_ptr() as *mut _,
                iov_len: data.len(),
            };

            file.write(&iov, 0x80).unwrap();
            file.sync().unwrap();

            let mut buf = vec![0u8; data.len()];
            let mut read_iov = libc::iovec {
                iov_base: buf.as_mut_ptr() as *mut _,
                iov_len: buf.len(),
            };

            file.read(&mut read_iov, 0x80).unwrap();
            assert_eq!(&buf, data);
        }

        #[test]
        fn ok_vectored_write_read_cycle() {
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x400, TEST_MID).unwrap();

            let mut bufs = [vec![1u8; 0x40], vec![2u8; 0x40]];
            let mut iovs: Vec<libc::iovec> = bufs
                .iter_mut()
                .map(|b| libc::iovec {
                    iov_base: b.as_mut_ptr() as *mut _,
                    iov_len: b.len(),
                })
                .collect();

            file.pwritev(&mut iovs, 0).unwrap();
            file.sync().unwrap();

            let mut read_bufs = [vec![0u8; 0x40], vec![0u8; 0x40]];
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
            let (_dir, path) = tmp_path();
            let file = Arc::new(FrozenFile::new(&path, 0x1000, TEST_MID).unwrap());

            let mut handles = vec![];
            for i in 0..0x0A {
                let f = file.clone();
                handles.push(std::thread::spawn(move || {
                    let data = vec![i as u8; 0x80];
                    let iov = libc::iovec {
                        iov_base: data.as_ptr() as *mut _,
                        iov_len: data.len(),
                    };

                    f.write(&iov, i * 0x80).unwrap();
                }));
            }

            for h in handles {
                h.join().unwrap();
            }

            file.sync().unwrap();

            for i in 0..0x0A {
                let mut buf = vec![0u8; 0x80];
                let mut iov = libc::iovec {
                    iov_base: buf.as_mut_ptr() as *mut _,
                    iov_len: buf.len(),
                };

                file.read(&mut iov, i * 0x80).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn ok_concurrent_grow_and_write() {
            let (_dir, path) = tmp_path();
            let file = Arc::new(FrozenFile::new(&path, 0x400, TEST_MID).unwrap());

            let writer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for i in 0..0x0Ausize {
                        let data = vec![i as u8; 0x40];
                        let iov = libc::iovec {
                            iov_base: data.as_ptr() as *mut _,
                            iov_len: data.len(),
                        };

                        f.write(&iov, i * 0x40).unwrap();
                    }
                })
            };

            let grower = {
                let f = file.clone();
                std::thread::spawn(move || {
                    f.grow(0x400).unwrap();
                })
            };

            writer.join().unwrap();
            grower.join().unwrap();

            file.sync().unwrap();
            assert_eq!(file.length().unwrap(), 0x800);

            for i in 0..0x0Ausize {
                let mut buf = vec![0u8; 0x40];
                let mut iov = libc::iovec {
                    iov_base: buf.as_mut_ptr() as *mut _,
                    iov_len: buf.len(),
                };

                file.read(&mut iov, i * 0x40).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn ok_concurrent_sync_and_write() {
            let (_dir, path) = tmp_path();
            let file = Arc::new(FrozenFile::new(&path, 0x800, TEST_MID).unwrap());

            let writer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for i in 0..16usize {
                        let data = vec![i as u8; 0x40];
                        let iov = libc::iovec {
                            iov_base: data.as_ptr() as *mut _,
                            iov_len: data.len(),
                        };

                        f.write(&iov, i * 0x40).unwrap();
                    }
                })
            };

            let syncer = {
                let f = file.clone();
                std::thread::spawn(move || {
                    for _ in 0..0x10 {
                        f.sync().unwrap();
                    }
                })
            };

            writer.join().unwrap();
            syncer.join().unwrap();

            file.sync().unwrap();

            for i in 0..0x10usize {
                let mut buf = vec![0u8; 0x40];
                let mut iov = libc::iovec {
                    iov_base: buf.as_mut_ptr() as *mut _,
                    iov_len: buf.len(),
                };

                file.read(&mut iov, i * 0x40).unwrap();
                assert!(buf.iter().all(|b| *b == i as u8));
            }
        }

        #[test]
        fn ok_write_does_not_chang_length() {
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x200, TEST_MID).unwrap();

            let initial_len = file.length().unwrap();
            assert_eq!(initial_len, 0x200);

            let data = [1u8; 0x40];
            let iov = libc::iovec {
                iov_base: data.as_ptr() as *mut _,
                iov_len: data.len(),
            };

            file.write(&iov, 0x80).unwrap();
            assert_eq!(file.length().unwrap(), initial_len);
        }

        #[test]
        fn err_read_hcf_for_eof() {
            let (_dir, path) = tmp_path();
            let file = FrozenFile::new(&path, 0x100, TEST_MID).unwrap();

            let mut buf = vec![0u8; 0x20];
            let mut iov = libc::iovec {
                iov_base: buf.as_mut_ptr() as *mut _,
                iov_len: buf.len(),
            };

            // offset >= length
            let err = file.read(&mut iov, 0x100).unwrap_err();
            assert!(err.cmp(FFileErrRes::Hcf as u16));
        }
    }
}
