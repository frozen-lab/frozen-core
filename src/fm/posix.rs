use super::{new_error, FMErr, FRes};
use core::{ptr, sync::atomic};
use libc::{
    c_void, mmap, msync, munmap, off_t, size_t, EACCES, EBADF, EBUSY, EINTR, EINVAL, EIO, ENOMEM, MAP_FAILED,
    MAP_SHARED, MS_SYNC, PROT_READ, PROT_WRITE,
};

/// Raw implementation of Posix (linux & macos) `memmap` for [`FrozenMMap`]
pub(super) struct POSIXMMap {
    ptr: *mut c_void,
    unmapped: atomic::AtomicBool,
}

unsafe impl Send for POSIXMMap {}
unsafe impl Sync for POSIXMMap {}

impl POSIXMMap {
    /// Create a new [`POSIXMMap`] instance for given `fd` w/ read & write permissions
    pub(super) unsafe fn new(fd: i32, length: size_t, mid: u8) -> FRes<Self> {
        let ptr = mmap(
            ptr::null_mut(),
            length,
            PROT_WRITE | PROT_READ,
            MAP_SHARED,
            fd,
            0 as off_t,
        );

        if ptr == MAP_FAILED {
            let error = last_os_error();
            let err_raw = error.raw_os_error();

            // invalid fd, invalid fd type, invalid length, etc.
            if err_raw == Some(EINVAL) || err_raw == Some(EBADF) || err_raw == Some(EACCES) {
                return new_error(mid, FMErr::Hcf, error);
            }

            // no more memory space available
            if err_raw == Some(ENOMEM) {
                return new_error(mid, FMErr::Nmm, error);
            }

            // unknown (unsupported, etc.)
            return new_error(mid, FMErr::Unk, error);
        }

        return Ok(Self {
            ptr,
            unmapped: atomic::AtomicBool::new(false),
        });
    }

    /// Unmap (free/drop) the mmaped instance of [`POSIXMMap`]
    pub(super) unsafe fn unmap(&self, length: usize, mid: u8) -> FRes<()> {
        // NOTE: To avoid another thread/process from executing munmap, we mark unmapped before even
        // trying to unmap, this kind of wroks like mutex, as we reassign to false on failure
        if self
            .unmapped
            .compare_exchange(false, true, atomic::Ordering::AcqRel, atomic::Ordering::Acquire)
            .is_err()
        {
            return Ok(());
        }

        if munmap(self.ptr, length) != 0 {
            let error = last_os_error();
            let err_raw = error.raw_os_error();

            // invalid or unaligned pointer
            if err_raw == Some(EINVAL) || err_raw == Some(ENOMEM) {
                return new_error(mid, FMErr::Hcf, error);
            }

            // unknown
            return new_error(mid, FMErr::Unk, error);
        }

        Ok(())
    }

    /// Syncs in-mem data on the storage device
    ///
    /// ## Durability on mac
    ///
    /// On mac, map sync (`msync(MS_SYNC)`) is not enough for crash durability, hence for
    /// harder durability guarantee, we must use `FrozenFile::sync` (i.e. `fcntl(F_FULLSYNC)`)
    pub(super) unsafe fn sync(&self, length: usize, mid: u8) -> FRes<()> {
        // only for EIO and EBUSY errors
        const MAX_RETRIES: usize = 4;
        let mut retries = 0;

        loop {
            if msync(self.ptr, length, MS_SYNC) != 0 {
                let error = last_os_error();
                let error_raw = error.raw_os_error();

                // IO interrupt (must retry)
                if error_raw == Some(EINTR) {
                    continue;
                }

                // invalid fd or lack of support for sync
                if error_raw == Some(ENOMEM) || error_raw == Some(EINVAL) {
                    return new_error(mid, FMErr::Hcf, error);
                }

                // locked file or fatel error, i.e. unable to sync
                //
                // NOTE: this is handled seperately, as if this error occurs, we must
                // notify users that the sync failed, hence the data is not persisted
                if error_raw == Some(EIO) || error_raw == Some(EBUSY) {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // retries exhausted and durability is broken in the current window
                    return new_error(mid, FMErr::Syn, error);
                }

                return new_error(mid, FMErr::Unk, error);
            }

            return Ok(());
        }
    }

    /// Get an immutable typed pointer to `T` at given `offset`
    #[inline]
    pub(super) unsafe fn get<T>(&self, offset: usize) -> *const T {
        self.ptr.add(offset) as *const T
    }

    /// Get a mutable (read/write) typed pointer to `T` at given `offset`
    #[inline]
    pub(super) unsafe fn get_mut<T>(&self, offset: usize) -> *mut T {
        self.ptr.add(offset) as *mut T
    }
}

// TODO: In future, make it `#![no_std]`
#[inline]
fn last_os_error() -> std::io::Error {
    std::io::Error::last_os_error()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fe::{FECheckOk, MID};
    use crate::ff::{FFCfg, FrozenFile};
    use std::path::PathBuf;
    use tempfile::{tempdir, TempDir};

    const LEN: usize = 0x80;

    fn get_ff_cfg(path: PathBuf) -> FFCfg {
        FFCfg::new(path, MID)
    }

    fn new_tmp() -> (TempDir, PathBuf, FrozenFile, POSIXMMap) {
        let dir = tempdir().expect("temp dir");
        let tmp = dir.path().join("tmp_file");

        unsafe {
            let file = FrozenFile::new(get_ff_cfg(tmp.clone()), LEN as u64).expect("new FrozenFile");
            let mmap = POSIXMMap::new(file.fd(), LEN, MID).expect("new POSIXMMap");

            (dir, tmp, file, mmap)
        }
    }

    mod mmap_new_and_unmap {
        use super::*;

        #[test]
        fn map_unmap_cycle() {
            let (_dir, _tmp, _file, map) = new_tmp();

            assert!(!map.ptr.is_null());
            assert!(unsafe { map.unmap(LEN, MID) }.check_ok());
        }

        #[test]
        fn map_fails_on_invalid_fd() {
            unsafe { assert!(POSIXMMap::new(-1, LEN, MID).is_err()) };
        }

        #[test]
        fn unmap_after_unmap_does_not_fails() {
            let (_dir, _tmp, _file, map) = new_tmp();

            unsafe {
                assert!(map.unmap(LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }
    }

    // NOTE: All the sync tests would pass on macos, as `msync` synchronizes kernel page cache
    // to fs, it just lacks stronger durability required in case of crash, etc.

    mod mmap_sync {
        use super::*;

        #[test]
        fn msync_works() {
            let (_dir, _tmp, _file, map) = new_tmp();

            unsafe {
                assert!(map.sync(LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn sync_persists_without_rewrite() {
            let (_dir, tmp, file, map) = new_tmp();

            unsafe {
                *map.get_mut::<u64>(16) = 0xABCD;

                assert!(map.sync(LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());

                drop(file);
            }

            unsafe {
                let file = FrozenFile::open(get_ff_cfg(tmp)).expect("open existing");
                let map = POSIXMMap::new(file.fd(), LEN, MID).expect("new mmap");

                assert_eq!(*map.get::<u64>(16), 0xABCD);
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn repeated_sync_is_stable() {
            let (_dir, _tmp, _file, map) = new_tmp();

            unsafe {
                *map.get_mut::<u64>(0) = 7;

                for _ in 0..0x20 {
                    assert!(map.sync(LEN, MID).check_ok());
                }

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn sync_after_unmap_should_fail_or_noop() {
            let (_dir, _tmp, _file, map) = new_tmp();

            unsafe {
                assert!(map.unmap(LEN, MID).check_ok());

                let res = map.sync(LEN, MID);
                assert!(res.is_err());
            }
        }
    }

    mod mmap_write_read {
        use super::*;

        #[test]
        fn write_read_cycle() {
            let (_dir, _tmp, _file, map) = new_tmp();

            unsafe {
                // write + sync
                let ptr = map.get_mut::<u64>(0);
                *ptr = 0xDEAD_C0DE_DEAD_C0DE;
                assert!(map.sync(LEN, MID).check_ok());

                // read + validate
                let val = *map.get::<u64>(0);
                assert_eq!(val, 0xDEAD_C0DE_DEAD_C0DE);

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn write_read_across_sessions() {
            let (_dir, tmp, file, map) = new_tmp();

            // write + sync + unmap + close
            unsafe {
                let ptr = map.get_mut::<u64>(0);
                *ptr = 0xDEAD_C0DE_DEAD_C0DE;
                assert!(map.sync(LEN, MID).check_ok());

                assert!(map.unmap(LEN, MID).check_ok());
                drop(file);
            }

            // open + map + read + validate
            unsafe {
                let file = FrozenFile::open(get_ff_cfg(tmp)).expect("open existing");
                let map = POSIXMMap::new(file.fd(), LEN, MID).expect("new mmap");

                // read + validate
                let val = *map.get::<u64>(0);
                assert_eq!(val, 0xDEAD_C0DE_DEAD_C0DE);

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn mmap_write_is_in_synced_with_file_read() {
            let (_dir, tmp, _file, map) = new_tmp();

            unsafe {
                // write + sync
                let ptr = map.get_mut::<u64>(0);
                *ptr = 0xDEAD_C0DE_DEAD_C0DE;
                assert!(map.sync(LEN, MID).check_ok());

                let buf = std::fs::read(&tmp).expect("read from file");
                let bytes: [u8; 8] = buf[0..8].try_into().expect("Slice with incorrect length");
                assert_eq!(u64::from_le_bytes(bytes), 0xDEAD_C0DE_DEAD_C0DE);

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn multiple_writes_single_sync() {
            let (_dir, _tmp, _file, map) = new_tmp();

            unsafe {
                for i in 0..16u64 {
                    *map.get_mut::<u64>((i as usize) * 8) = i;
                }

                assert!(map.sync(LEN, MID).check_ok());

                for i in 0..16u64 {
                    assert_eq!(*map.get::<u64>((i as usize) * 8), i);
                }

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }
    }

    mod mmap_concurrency {
        use super::*;
        use std::{sync, thread};

        #[test]
        fn munmap_is_thread_safe() {
            let (_dir, _tmp, _file, map) = new_tmp();

            let mut handles = Vec::new();
            let map = sync::Arc::new(map);

            for _ in 0..8 {
                let m = map.clone();
                handles.push(thread::spawn(move || unsafe {
                    assert!(m.unmap(LEN, MID).check_ok());
                }));
            }

            for h in handles {
                assert!(h
                    .join()
                    .map_err(|e| {
                        eprintln!("\n{:?}\n", e);
                    })
                    .is_ok());
            }
        }

        #[test]
        fn msync_is_thread_safe() {
            let (_dir, _tmp, _file, map) = new_tmp();

            let mut handles = Vec::new();
            let map = sync::Arc::new(map);

            unsafe {
                *map.get_mut::<u64>(0) = 42;
            }

            for _ in 0..8 {
                let m = map.clone();
                handles.push(thread::spawn(move || unsafe {
                    assert!(m.sync(LEN, MID).check_ok());
                }));
            }

            for h in handles {
                assert!(h
                    .join()
                    .map_err(|e| {
                        eprintln!("\n{:?}\n", e);
                    })
                    .is_ok());
            }

            unsafe {
                assert_eq!(*map.get::<u64>(0), 42);
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn concurrent_writes_then_sync() {
            let (_dir, _tmp, _file, map) = new_tmp();

            let mut handles = Vec::new();
            let map = sync::Arc::new(map);

            for i in 0..8u64 {
                let m = map.clone();
                handles.push(thread::spawn(move || unsafe {
                    let ptr = m.get_mut::<u64>(0);
                    *ptr = i;
                }));
            }

            for h in handles {
                assert!(h
                    .join()
                    .map_err(|e| {
                        eprintln!("\n{:?}\n", e);
                    })
                    .is_ok());
            }

            unsafe {
                assert!(map.sync(LEN, MID).check_ok());
                assert!(map.unmap(LEN, MID).check_ok());
            }
        }

        #[test]
        fn concurrent_writes_distinct_offsets() {
            let (_dir, _tmp, _file, map) = new_tmp();

            let mut handles = Vec::new();
            let map = std::sync::Arc::new(map);

            for i in 0..8u64 {
                let m = map.clone();
                handles.push(std::thread::spawn(move || unsafe {
                    *m.get_mut::<u64>((i as usize) * 8) = i;
                }));
            }

            for h in handles {
                h.join().expect("thread join failed");
            }

            unsafe {
                assert!(map.sync(LEN, MID).check_ok());

                for i in 0..8u64 {
                    assert_eq!(*map.get::<u64>((i as usize) * 8), i);
                }

                assert!(map.unmap(LEN, MID).check_ok());
            }
        }
    }
}
