use super::{new_err, FMMapErrRes, ObjectInterface};
use crate::{error::FrozenRes, hints};
use core::{ffi::CStr, ptr};
use libc::{
    c_void, mmap, msync, munmap, off_t, size_t, strerror, EACCES, EBADF, EBUSY, EINTR, EINVAL, EIO, ENOMEM, EOVERFLOW,
    MAP_FAILED, MAP_SHARED, MS_SYNC, PROT_READ, PROT_WRITE,
};

type TPtr = *mut c_void;

/// max allowed retries for `EINTR` errors
const MAX_RETRIES: usize = 0x0A;

/// Custom impl of `mmap(2)` for POSIX systems
#[derive(Debug)]
pub(super) struct POSIXMMap(TPtr);

unsafe impl Send for POSIXMMap {}
unsafe impl Sync for POSIXMMap {}

impl POSIXMMap {
    /// Create a new [`POSIXMMap`] w/ given `fd` and `length`
    pub(super) unsafe fn new(fd: i32, length: size_t) -> FrozenRes<Self> {
        let ptr = mmap_raw(fd, length)?;
        Ok(Self(ptr))
    }

    /// Close [`POSIXMMap`] to give up allocated resources
    pub(super) unsafe fn unmap(&self, length: usize) -> FrozenRes<()> {
        munmap_raw(self.0, length)
    }

    /// Syncs in cache data updates on the storage device
    ///
    /// ## Durability
    ///
    /// In POSIX systems `msync(MS_SYNC)`, does not provide crash safe durability, this syscall is used
    /// as a best-effort operation, to explicitly push dirty mmaped pages into fs writeback
    ///
    /// For strong durability, use of [`FrozenFile::sync`] is required, right after calling [`FrozenMMap::sync`]
    ///
    /// ## Why do we retry?
    ///
    /// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases, no progress
    /// is guaranteed, so the syscall must be retried
    pub(super) unsafe fn sync(&self, length: usize) -> FrozenRes<()> {
        msync_raw(self.0, length)
    }

    /// Get a mutable (read/write) typed pointer to `T` at given `offset`
    ///
    /// Given `offset` must be aligned w/ `std::mem::size_of::<ObjectInterface<T>>()`
    #[inline]
    pub(super) unsafe fn as_ptr<T>(&self, offset: usize) -> *mut ObjectInterface<T>
    where
        T: Sized + Send + Sync,
    {
        self.0.add(offset) as *mut ObjectInterface<T>
    }
}

/// create a new memory mapping w/ `mmap(2)` on given `fd` and `length`
///
/// ## Caveats of `mmap(2)` on POSIX
///
/// In POSIX systems, when calling `mmap(2)`, the provided offset must be multiple of page size,
/// i.e. `sysconf(_SC_PAGESIZE)`, otherwise an `EINVAL` error is thrown
///
/// For our usecase, we always map the entire file, hence this is never an issue for us
unsafe fn mmap_raw(fd: i32, length: size_t) -> FrozenRes<TPtr> {
    let ptr = mmap(
        ptr::null_mut(),
        length,
        PROT_WRITE | PROT_READ,
        MAP_SHARED,
        fd,
        0 as off_t,
    );

    if ptr == MAP_FAILED {
        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // invalid fd, invalid fd type, invalid length, etc.
            EINVAL | EBADF | EACCES | EOVERFLOW => return new_err(FMMapErrRes::Hcf, err_msg),

            // no more memory available
            ENOMEM => return new_err(FMMapErrRes::Nmm, err_msg),

            _ => return new_err(FMMapErrRes::Unk, err_msg),
        };
    }

    Ok(ptr)
}

/// unmap the created memory mapping w/ `mummap(2)` by given ref `ptr` and `length`
unsafe fn munmap_raw(ptr: TPtr, length: size_t) -> FrozenRes<()> {
    if munmap(ptr, length) == 0 {
        return Ok(());
    }

    let errno = last_errno();
    let err_msg = err_msg(errno);

    match errno {
        // invalid/unaligned ptr or address range is not mapped
        EINVAL | ENOMEM => new_err(FMMapErrRes::Hcf, err_msg),

        _ => new_err(FMMapErrRes::Unk, err_msg),
    }
}

/// Syncs in cache data updates on the storage device
///
/// ## Caveats of `msync(2)` on POSIX
///
/// This syscall by itself does not provide any durability guarantee, it's used as best-effort operation
/// to explicitly push dirty mmaped pages into fs writeback, to aid hard sync calls like `fdatasync` on linux
/// and `fnctl(F_FULLSYNC)` on mac
unsafe fn msync_raw(ptr: TPtr, length: size_t) -> FrozenRes<()> {
    let mut retries = 0; // only for EINTR errors
    loop {
        let res = msync(ptr, length, MS_SYNC);
        if hints::likely(res == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt, locked file or fatel error
            EINTR | EBUSY => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_err(FMMapErrRes::Syn, err_msg);
            }

            // fatal error, i.e. no sync for writes in recent window/batch
            EIO => return new_err(FMMapErrRes::Syn, err_msg),

            // invalid fd or lack of support for sync
            EINVAL => return new_err(FMMapErrRes::Hcf, err_msg),

            // no-more memory available
            ENOMEM => return new_err(FMMapErrRes::Nmm, err_msg),

            _ => return new_err(FMMapErrRes::Unk, err_msg),
        }
    }
}

#[inline]
fn last_errno() -> i32 {
    #[cfg(target_os = "linux")]
    unsafe {
        *libc::__errno_location()
    }

    #[cfg(target_os = "macos")]
    unsafe {
        *libc::__error()
    }
}

#[inline]
unsafe fn err_msg(errno: i32) -> Vec<u8> {
    let ptr = strerror(errno);
    if ptr.is_null() {
        return Vec::new();
    }

    CStr::from_ptr(ptr).to_bytes().to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        error::TEST_MID,
        ffile::{FFCfg, FrozenFile},
    };

    const CHUNK: usize = 0x10;
    const INIT_CHUNKS: usize = 0x0A;
    const LENGTH: usize = CHUNK * INIT_CHUNKS;

    fn new_tmp() -> (tempfile::TempDir, FrozenFile) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tmp_map");

        let cfg = FFCfg {
            path,
            mid: TEST_MID,
            chunk_size: CHUNK,
            initial_chunk_amount: INIT_CHUNKS,
        };
        let file = FrozenFile::new(cfg).expect("new FF");

        (dir, file)
    }

    mod map_umap {
        use super::*;

        #[test]
        fn ok_map_unmap_cycle() {
            let (_dir, file) = new_tmp();

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();
                mmap.unmap(LENGTH).unwrap();
            }
        }

        #[test]
        fn ok_map_zero_bytes_on_new() {
            let (_dir, file) = new_tmp();
            const BUF: [u8; LENGTH] = [0; LENGTH];

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();

                let ptr = mmap.as_ptr::<[u8; LENGTH]>(0);
                let oi = &*ptr;
                assert_eq!(*oi.get(), BUF);

                mmap.unmap(LENGTH).unwrap();
            }
        }

        #[test]
        fn err_map_on_invalid_length() {
            let (_dir, file) = new_tmp();

            unsafe {
                let err = POSIXMMap::new(file.fd(), 0).unwrap_err();
                assert!(err.cmp(FMMapErrRes::Hcf as u16));
            }
        }

        #[test]
        fn err_map_on_invalid_fd() {
            let (_dir, _) = new_tmp();

            unsafe {
                let err = POSIXMMap::new(-1, LENGTH).unwrap_err();
                assert!(err.cmp(FMMapErrRes::Hcf as u16));
            }
        }

        #[test]
        fn err_unmap_on_invalid_length() {
            let (_dir, file) = new_tmp();

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();
                let err = mmap.unmap(0).unwrap_err();
                assert!(err.cmp(FMMapErrRes::Hcf as u16));
            }
        }
    }

    mod utils {
        use super::*;

        #[test]
        fn ok_last_errno() {
            unsafe {
                let _ = libc::close(-1);
                assert_eq!(last_errno(), libc::EBADF);
            }
        }

        #[test]
        fn ok_err_msg() {
            unsafe {
                let msg = err_msg(libc::ENOENT);
                assert!(!msg.is_empty(), "ENOENT must produce message");
            }
        }
    }

    mod map_sync {
        use super::*;

        #[test]
        fn ok_sync() {
            let (_dir, file) = new_tmp();

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();
                mmap.sync(LENGTH).unwrap();
                mmap.unmap(LENGTH).unwrap();
            }
        }

        #[test]
        fn ok_sync_after_sync() {
            let (_dir, file) = new_tmp();

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();

                mmap.sync(LENGTH).unwrap();
                mmap.sync(LENGTH).unwrap();
                mmap.sync(LENGTH).unwrap();
                mmap.sync(LENGTH).unwrap();

                mmap.unmap(LENGTH).unwrap();
            }
        }
    }

    mod map_write_read {
        use super::*;

        #[test]
        fn ok_write_read_cycle() {
            let (_dir, file) = new_tmp();
            const VAL: u32 = 0xDEADC0DE;

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();

                // write
                let wptr = mmap.as_ptr::<u32>(0);
                let oi = &*wptr;
                *oi.get_mut() = VAL;

                // read
                let rptr = mmap.as_ptr::<u32>(0);
                let oi = &*rptr;
                assert_eq!(*oi.get(), VAL);

                mmap.unmap(LENGTH).unwrap();
            }
        }

        #[test]
        fn ok_write_read_with_offset() {
            let (_dir, file) = new_tmp();
            const VAL: u32 = 0xDEADC0DE;

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();

                // write
                let wptr = mmap.as_ptr::<u32>(0x0C);
                let oi = &*wptr;
                *oi.get_mut() = VAL;

                // read
                let rptr = mmap.as_ptr::<u32>(0x0C);
                let oi = &*rptr;
                assert_eq!(*oi.get(), VAL);

                mmap.unmap(LENGTH).unwrap();
            }
        }

        #[test]
        fn ok_write_read_sync_cycle() {
            let (_dir, file) = new_tmp();
            const VAL: [u32; 0x0A] = [0xDEADC0DE; 0x0A];

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();

                // write
                let wptr = mmap.as_ptr::<[u32; 0x0A]>(0x0C);
                let oi = &*wptr;
                *oi.get_mut() = VAL;

                // sync
                mmap.sync(LENGTH).unwrap();

                // read
                let rptr = mmap.as_ptr::<[u32; 0x0A]>(0x0C);
                let oi = &*rptr;
                assert_eq!(*oi.get(), VAL);

                mmap.unmap(LENGTH).unwrap();
            }
        }

        #[test]
        fn ok_read_zero_bytes() {
            let (_dir, file) = new_tmp();

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();

                let rptr = mmap.as_ptr::<u64>(0);
                let oi = &*rptr;
                assert_eq!(*oi.get(), 0);

                mmap.unmap(LENGTH).unwrap();
            }
        }
    }

    mod map_durability {
        use super::*;

        #[test]
        fn ok_map_durability_after_unmap() {
            let (_dir, file) = new_tmp();
            const VAL: u64 = 0xCAFEBABEDEADC0DE;

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();

                let ptr = mmap.as_ptr::<u64>(0);
                *(&*ptr).get_mut() = VAL;

                mmap.sync(LENGTH).unwrap();
                mmap.unmap(LENGTH).unwrap();
            }

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();

                let ptr = mmap.as_ptr::<u64>(0);
                assert_eq!(*(&*ptr).get(), VAL);

                mmap.unmap(LENGTH).unwrap();
            }
        }

        #[test]
        fn ok_map_durability_after_unmap_and_close() {
            let (dir, file) = new_tmp();
            const VAL: u64 = 0xCAFEBABEDEADC0DE;

            unsafe {
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();

                let ptr = mmap.as_ptr::<u64>(0);
                *(&*ptr).get_mut() = VAL;

                mmap.sync(LENGTH).unwrap();
                mmap.unmap(LENGTH).unwrap();
                drop(file);
            }

            unsafe {
                let path = dir.path().join("tmp_map");
                let cfg = FFCfg {
                    mid: TEST_MID,
                    path,
                    chunk_size: CHUNK,
                    initial_chunk_amount: INIT_CHUNKS,
                };

                let file = FrozenFile::new(cfg).expect("new FF");
                let mmap = POSIXMMap::new(file.fd(), LENGTH).unwrap();

                let ptr = mmap.as_ptr::<u64>(0);
                assert_eq!(*(&*ptr).get(), VAL);

                mmap.unmap(LENGTH).unwrap();
            }
        }
    }
}
