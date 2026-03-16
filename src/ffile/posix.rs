use super::{err, new_err, new_err_default, TFileId};
use crate::{error::FrozenRes, hints};
use libc::{
    access, c_int, c_uint, c_void, close, flock, fstat, ftruncate, iovec, off_t, open, pread, preadv, pwrite, pwritev,
    size_t, stat, strerror, sysconf, unlink, EACCES, EAGAIN, EBADF, EFAULT, EINTR, EINVAL, EIO, EISDIR, EMSGSIZE,
    ENOENT, ENOLCK, ENOSPC, ENOTDIR, EOPNOTSUPP, EPERM, EROFS, ESPIPE, EWOULDBLOCK, F_OK, LOCK_EX, LOCK_NB, O_CLOEXEC,
    O_CREAT, O_DIRECTORY, O_RDONLY, O_RDWR, S_IRUSR, S_IWUSR, _SC_IOV_MAX,
};
use std::{
    ffi::CStr,
    mem,
    sync::{atomic, OnceLock},
};

static IOV_MAX_CACHE: OnceLock<usize> = OnceLock::new();

/// placeholder value for when current fd is closed
pub(in crate::ffile) const CLOSED_FD: TFileId = TFileId::MIN;

/// max allowed retries for `EINTR` errors
const MAX_RETRIES: usize = 0x0A;

/// max iovecs allowed for single readv/writev calls
const MAX_IOVECS: usize = 0x200;

/// Maximum number of [`libc::iovec`] descriptors allocated on the stack
const STACK_IOV: usize = 0x40;

/// Custom impl of `std::fs::File` for POSIX systems
#[derive(Debug)]
pub(super) struct POSIXFile(atomic::AtomicI32);

unsafe impl Send for POSIXFile {}
unsafe impl Sync for POSIXFile {}

impl POSIXFile {
    /// Read file descriptor of [`POSIXFile`]
    #[inline]
    pub(super) fn fd(&self) -> TFileId {
        self.0.load(atomic::Ordering::Acquire)
    }

    /// Check if [`POSIXFile`] exists on storage device or not
    ///
    /// ## How it works
    ///
    /// By using `access(path)` syscall w/ `F_OK`, we check whether the calling process
    /// can resolve the given `path` in underlying fs
    pub(super) unsafe fn exists(path: &std::path::Path) -> FrozenRes<bool> {
        let cpath = path_to_cstring(path)?;
        Ok(access(cpath.as_ptr(), F_OK) == 0)
    }

    /// Create a new or open an existing [`POSIXFile`]
    ///
    /// ## Crash safe durability
    ///
    /// In POSIX systems, `open(O_CREATE)` only creates the directory entry in memory, it may be
    /// visible immediately, but the file entry is not crash durable on many fs
    ///
    /// On some linux systems, journaling fs (ext4, xfs, etc) often replay their journal on mount
    /// after a crash is observed, which usually restores recent directory updates, i.e. our newly created
    /// file entry, as a result newly created file often survive the crash
    ///
    /// In our case, when a new [`FrozenFile`] is created, we zero-extend it using `ftruncate()`,
    /// and perform `fdatasync()` or `fcntl(F_FULLSYNC)`, which in result provides us the crash safe
    /// durability we need
    pub(super) unsafe fn new(path: &std::path::Path) -> FrozenRes<Self> {
        let fd = open_raw(path, prep_flags())?;

        // best-effort call to provide a hint to the kernel that the file will be accessed in a random pattern
        #[cfg(target_os = "linux")]
        f_advise_raw(fd)?;

        Ok(Self(atomic::AtomicI32::new(fd)))
    }

    /// Acquire an exclusive advisory lock on [`POSIXFile`]
    ///
    /// ## Purpose
    ///
    /// We must ensure that only a single [`POSIXFile`] instance, across all processes, can operate on
    /// the underlying file, at a given time
    ///
    /// So, we acquire an exclusive lock, for the entire file, after open, so if another process tries,
    /// it could hault or choose not to exists anymore, to avoid multiple open handles across the same
    /// underlying file
    ///
    /// ## Advisory Semantics
    ///
    /// We use `flock(fd)`, which provides advisory locking only, the kernel does not prevent
    /// other processes from calling `open()`, but any cooperating process attempting
    /// to acquire the same exclusive lock will fail with `EWOULDBLOCK` i.e. [`err::LCK`]
    ///
    /// ## Why do we retry?
    ///
    /// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases no progress is
    /// guaranteed, so the syscall must be retried
    pub(super) unsafe fn flock(&self) -> FrozenRes<()> {
        flock_raw(self.fd())
    }

    /// Close [`POSIXFile`] to give up allocated resources
    ///
    /// This function is idempotent, hence it prevents close-on-close errors
    ///
    /// ## Sync Error (`err::SYN`)
    ///
    /// In POSIX systems, kernel may report delayed write/sync failures when closing, this are
    /// durability errors, fatal for us
    ///
    /// we can easily tackle this error for each bach of writes by enforcing hard durability
    /// guaranties right after the write ops, and making sure they are completed without errors
    ///
    /// this provides strong durability for the storage engine, and if `EIO` occurs, anyhow,
    /// we treat it as `err::HCF` i.e. impl failure
    pub(super) unsafe fn close(&self) -> FrozenRes<()> {
        let fd = self.0.swap(CLOSED_FD, atomic::Ordering::AcqRel);
        if fd == CLOSED_FD {
            return Ok(());
        }

        close_raw(fd)
    }

    /// Deletes the [`POSIXFile`] entery from the fs
    pub(super) unsafe fn unlink(&self, path: &std::path::Path) -> FrozenRes<()> {
        let cpath = path_to_cstring(path)?;

        // NOTE: POSIX systems requires fd to be closed before attempting to unlink the file
        self.close()?;

        if unlink(cpath.as_ptr()) == 0 {
            // NOTE: In POSIX systems, `unlink(path)` only updates the entry in memory, and
            // does not guaranty crash safe durability for the operation, we must perform
            // `fsync` on the directory to make sure we get crash safe durability
            return sync_parent_dir(path);
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // missing file or invalid path
            ENOENT | ENOTDIR => new_err(err::INV, err_msg),

            // lack of permission or read only fs
            EACCES | EPERM | EROFS => new_err(err::PRM, err_msg),

            // NOTE: In POSIX systems, kernel may report delayed io failures on `unlink`,
            // this are fatal errors, and can not be retried
            //
            // We protect this by enforcing hard durability right after write ops, so the
            // occurrence of this error is an implementation failure
            EIO => new_err(err::HCF, err_msg),

            _ => new_err(err::UNK, err_msg),
        }
    }

    /// Read current length of [`POSIXFile`] using file metadata (w/ `fstat` syscall)
    pub(super) unsafe fn length(&self) -> FrozenRes<usize> {
        let mut st = core::mem::zeroed::<stat>();
        let res = fstat(self.fd(), &mut st);

        if res != 0 {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            // bad or invalid fd
            if errno == EBADF || errno == EFAULT {
                return new_err(err::HCF, err_msg);
            }

            return new_err(err::UNK, err_msg);
        }

        Ok(st.st_size as usize)
    }

    /// Grow (zero extend) [`POSIXFile`] w/ given `len_to_add`
    ///
    /// ## Semantics
    ///
    /// Here `grow()` is not atomic in all or nothing sense, following scenerios may happen,
    ///
    /// - on linux `fallocate` may fail, but `ftruncate` succeeds
    /// - on mac `ftruncate` succeeds but `f_preallocate` may fail
    /// - and on both `ftruncate` may also fail
    ///
    /// in all these scenerios, either the `st_size` is correctly updated or not updated at all
    ///
    /// if either of `fallocate` or `f_preallocate` has failed, not supported by fs, etc. as long as
    /// `ftruncate` succeeds, our future write ops (pwrite and pwritev) will work fine, this is mainly
    /// cause `fallocate` and `f_preallocate` are best-effort operations for us to reduce the latency
    /// for write ops
    pub(super) unsafe fn grow(&self, curr_len: usize, len_to_add: usize) -> FrozenRes<()> {
        let fd = self.fd();

        // NOTE: On linux, `fallocate` must be called before the `ftruncate` to handle `ENOSPC`,
        // when the order is revered, the file length may be updated despite the failure to allocate
        // space on fs, which may fail all the future write ops
        #[cfg(target_os = "linux")]
        fallocate_raw(fd, curr_len, len_to_add)?;

        ftruncate_raw(fd, curr_len, len_to_add)?;

        // INFO: On mac, we can hint the kernel to allocate disk space for the added `len_to_add`,
        // to reduce the latency of future write ops (must always be called after `ftruncate` on mac)
        #[cfg(target_os = "macos")]
        f_preallocate_raw(fd, curr_len, len_to_add)?;

        Ok(())
    }

    /// Syncs in cache data updates on the storage device
    ///
    /// ## Why do we retry?
    ///
    /// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases no progress is
    /// guaranteed, so the syscall must be retried
    ///
    /// ## `F_FULLFSYNC` vs `fsync`
    ///
    /// The supposed best os, i.e. mac, does not provide strong durability via `fsync()`, hence writes/updates
    /// may lost on crash or power failure, as it does not provide strong durability (instant flush), read docs for
    /// more info [https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/fsync.2.html]
    ///
    /// To achieve true crash durability (including protection against power loss, sudden crash), we have to use
    /// the `fcntl(fd, F_FULLFSYNC)` syscall
    ///
    /// ## Fallback to `fsync`
    ///
    /// `fcntl(F_FULLSYNC)` may result in `EINVAL` or `ENOTSUP` on fs which may not support it, such as network fs,
    /// FUSE mounts, FAT32 volumes, or some external devices
    ///
    /// To guard this, we fallback to `fsync()`, which does not guaranty durability for sudden crash or
    /// power loss, which is acceptable when strong durability is simply not available or allowed
    #[cfg(target_os = "macos")]
    pub(super) unsafe fn sync(&self) -> FrozenRes<()> {
        f_fullsync_raw(self.fd())
    }

    /// Syncs in cache data updates on the storage device
    ///
    /// ## Why do we retry?
    ///
    /// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases no progress is
    /// guaranteed, so the syscall must be retried
    ///
    /// ## `fsync` vs `fdatasync`
    ///
    /// We use `fdatasync()` instead of `fsync()` for persistence, as it guarantees, all updates/writes and
    /// any metadata, such as file size, are flushed to stable storage
    ///
    /// With combonation of `O_NOATIME` and `fdatasync()`, we avoid non-essential metadata updates, such as
    /// access time (`atime`), modification time (`mtime`), and other bookkeeping info
    #[cfg(target_os = "linux")]
    pub(super) unsafe fn sync(&self) -> FrozenRes<()> {
        fdatasync_raw(self.fd())
    }

    /// Initiates writeback (best-effort) of dirty pages in the specified range
    ///
    /// ## Purpose
    ///
    /// In our case, `sync_range` is used as a prompt for the kernel to start flushing dirty pages in the
    /// specified range, which result in reduced latency for `fdatasync` and `fcntl(F_FULLSYNC)` syscalls
    ///
    /// This syscall, by itself, does not guarantee any kind of durability, and must always be paired with
    /// strong sync calls like `fdatasync()` and `fcntl(F_FULLSYNC)`
    ///
    /// ## Why do we retry?
    ///
    /// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases no progress is
    /// guaranteed, so the syscall must be retried
    #[cfg(target_os = "linux")]
    pub(super) unsafe fn sync_range(&self, offset: usize, len: usize) -> FrozenRes<()> {
        sync_file_range_raw(self.fd(), offset, len)
    }

    /// Read a single chunk from given `offset` w/ `pread` syscall
    #[inline(always)]
    pub(super) unsafe fn pread(&self, ptr: *mut u8, offset: usize, chunk_size: usize) -> FrozenRes<()> {
        let fd = self.fd();

        let mut read = 0usize;
        while read < chunk_size {
            let res = pread(
                fd,
                ptr.add(read) as *mut c_void,
                (chunk_size - read) as size_t,
                (offset + read) as off_t,
            );

            // unexpected EOF
            if res == 0 {
                // NOTE: we treat this as `Hcf` error cause, this only occurs when we tried to read
                // beyound current length of the file, which is result of invalid impl
                return new_err_default(err::HCF);
            }

            if hints::unlikely(res < 0) {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    // io interrupt
                    EINTR | EAGAIN => continue,

                    // permission denied
                    EACCES | EPERM => return new_err(err::RED, err_msg),

                    // invalid fd, invalid fd type, bad pointer, etc.
                    EINVAL | EBADF | EFAULT | ESPIPE => return new_err(err::HCF, err_msg),

                    _ => return new_err(err::UNK, err_msg),
                }
            }

            read += res as usize;
        }

        Ok(())
    }

    /// Write a single chunk at given `offset` w/ `pwrite` syscall
    #[inline(always)]
    pub(super) unsafe fn pwrite(&self, ptr: *mut u8, offset: usize, chunk_size: usize) -> FrozenRes<()> {
        let fd = self.fd();

        let mut written = 0usize;
        while written < chunk_size {
            let res = pwrite(
                fd,
                ptr.add(written) as *mut c_void,
                (chunk_size - written) as size_t,
                (offset + written) as off_t,
            );

            // unexpected EOF
            if res == 0 {
                return new_err_default(err::HCF);
            }

            if hints::unlikely(res < 0) {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    // io interrupt
                    EINTR | EAGAIN => continue,

                    // permission denied or read-only file
                    EACCES | EPERM | EROFS => return new_err(err::WRT, err_msg),

                    // invalid fd, invalid fd type, bad pointer, etc.
                    EINVAL | EBADF | EFAULT | ESPIPE => return new_err(err::HCF, err_msg),

                    _ => return new_err(err::UNK, err_msg),
                }
            }

            written += res as usize;
        }

        Ok(())
    }

    /// Read multiple chunk objects starting from given `offset` w/ `preadv` syscall
    ///
    /// ## NOTES
    ///
    /// - All chunks in given bufs slice must be of same length
    /// - The caller must not try to read byound current length of `[POSIXFile]`
    #[inline(always)]
    pub(super) unsafe fn preadv(&self, bufs: &[*mut u8], offset: usize, chunk_size: usize) -> FrozenRes<()> {
        let fd = self.fd();
        let max_iovs = read_max_iovecs();

        let (mut heap, mut stack) = build_iovecs(bufs, chunk_size);
        let (iov_ptr, iovs_len) = if let Some(ref mut s) = stack {
            (s.as_mut_ptr(), bufs.len())
        } else {
            (heap.as_mut_ptr(), heap.len())
        };

        let mut head = 0usize;
        let mut off = offset as off_t;

        while head < iovs_len {
            let remaining_iov = iovs_len - head;
            let cnt = remaining_iov.min(max_iovs) as c_int;
            let ptr = iov_ptr.add(head);

            let res = preadv(fd, ptr, cnt, off);

            // unexpected EOF
            if res == 0 {
                // NOTE: we treat this as `Hcf` error cause, this only occurs when we tried to read
                // beyound current length of the file, which is result of invalid impl
                return new_err_default(err::HCF);
            }

            if res < 0 {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    EINTR | EAGAIN => continue,

                    // permission denied
                    EACCES | EPERM => return new_err(err::RED, err_msg),

                    // invalid fd, bad pointer, illegal seek, etc.
                    EINVAL | EBADF | EFAULT | ESPIPE | EMSGSIZE => return new_err(err::HCF, err_msg),

                    _ => return new_err(err::UNK, err_msg),
                }
            }

            // NOTE:
            //
            // In POSIX systems, preadv syscall may,
            // - read fewer bytes than requested
            // - stop in-between iovec's
            // - stop mid iovec
            //
            // even though this behavior is situation and fs dependent (well, according to my short research),
            // we opt to handle it for correctness across different systems

            off += res as off_t;

            let read = res as usize;
            let partial = read % chunk_size;
            let full_pages = read / chunk_size;

            // fully written pages
            head += full_pages;

            // partially written page (rare)
            if partial > 0 && head < iovs_len {
                let iov = &mut *iov_ptr.add(head);
                iov.iov_base = (iov.iov_base as *mut u8).add(partial) as *mut c_void;
                iov.iov_len -= partial;
            }
        }

        Ok(())
    }

    /// Write multiple chunk objects starting from given `offset` w/ `writev` syscall
    ///
    /// ## NOTES
    ///
    /// - All chunk objects in given slice must be of same length
    /// - The caller must not try to write byound current length of `[POSIXFile]`
    #[inline(always)]
    pub(super) unsafe fn pwritev(&self, bufs: &[*mut u8], offset: usize, chunk_size: usize) -> FrozenRes<()> {
        let fd = self.fd();
        let max_iovs = read_max_iovecs();

        let (mut heap, mut stack) = build_iovecs(bufs, chunk_size);
        let (iov_ptr, iovs_len) = if let Some(ref mut s) = stack {
            (s.as_mut_ptr(), bufs.len())
        } else {
            (heap.as_mut_ptr(), heap.len())
        };

        let mut head = 0usize;
        let mut off = offset as off_t;

        while head < iovs_len {
            let remaining_iov = iovs_len - head;
            let cnt = remaining_iov.min(max_iovs) as c_int;
            let ptr = iov_ptr.add(head);

            let res = pwritev(fd, ptr, cnt, off);

            // unexpected EOF
            if res == 0 {
                return new_err_default(err::HCF);
            }

            if res < 0 {
                let errno = last_errno();
                let err_msg = err_msg(errno);

                match errno {
                    EINTR | EAGAIN => continue,

                    // permission denied
                    EACCES | EPERM => return new_err(err::WRT, err_msg),

                    // invalid fd, bad pointer, illegal seek, etc.
                    EINVAL | EBADF | EFAULT | ESPIPE | EMSGSIZE => return new_err(err::HCF, err_msg),

                    _ => return new_err(err::UNK, err_msg),
                }
            }

            // NOTE:
            //
            // In POSIX systems, pwritev syscall may,
            // - write fewer bytes than requested
            // - stop in-between iovec's
            // - stop mid iovec
            //
            // even though this behavior is situation and fs dependent (well, according to my short research),
            // we opt to handle it for correctness across different systems

            off += res as off_t;

            let written = res as usize;
            let partial = written % chunk_size;
            let full_pages = written / chunk_size;

            // fully written pages
            head += full_pages;

            // partially written page (rare)
            if partial > 0 && head < iovs_len {
                let iov = &mut *iov_ptr.add(head);
                iov.iov_base = (iov.iov_base as *mut u8).add(partial) as *mut c_void;
                iov.iov_len -= partial;
            }
        }

        Ok(())
    }
}

/// create/open a new file w/ `open` syscall
///
/// ## Caveats of `O_NOATIME` (`EPERM` err_msg)
///
/// `open()` with `O_NOATIME` may fail with `EPERM` instead of silently ignoring the flag
///
/// `EPERM` indicates a kernel level permission violation, as the kernel rejects the
/// request outright, even though the flag only affects metadata behavior
///
/// To remain sane across ownership models, containers, and shared filesystems,
/// we explicitly retry the `open()` w/o `O_NOATIME` when `EPERM` is encountered
unsafe fn open_raw(path: &std::path::Path, flags: c_int) -> FrozenRes<TFileId> {
    let cpath = path_to_cstring(path)?;

    // write + read permissions
    let perm = (S_IRUSR | S_IWUSR) as c_uint;

    #[cfg(target_os = "linux")]
    let (mut flags, mut tried_noatime) = (flags, false);

    let mut retries = 0; // only for EINTR errors
    loop {
        let fd = if flags & O_CREAT != 0 {
            open(cpath.as_ptr(), flags, perm)
        } else {
            open(cpath.as_ptr(), flags)
        };

        if hints::unlikely(fd < 0) {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            // NOTE: if the error is EPERM and flags contains O_NOATIME flag, we try to open again
            // w/o the O_NOATIME flag, as some fs does not support this flag

            #[cfg(target_os = "linux")]
            if errno == EPERM && (flags & libc::O_NOATIME) != 0 && !tried_noatime {
                flags &= !libc::O_NOATIME;
                tried_noatime = true;
                continue;
            }

            match errno {
                // NOTE: We must retry on interuption errors (EINTR retry)
                EINTR | EAGAIN => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    return new_err(err::UNK, err_msg);
                }

                // no space available on disk
                ENOSPC => return new_err(err::NSP, err_msg),

                // path is a dir (hcf)
                EISDIR => return new_err(err::HCF, err_msg),

                // invalid path (missing sub dir's)
                ENOENT | ENOTDIR => return new_err(err::INV, err_msg),

                // permission denied or read-only fs
                EACCES | EPERM | EROFS => return new_err(err::PRM, err_msg),

                _ => return new_err(err::UNK, err_msg),
            }
        }

        return Ok(fd);
    }
}

unsafe fn close_raw(fd: TFileId) -> FrozenRes<()> {
    if close(fd) == 0 {
        return Ok(());
    }

    let errno = last_errno();
    let err_msg = err_msg(errno);

    // POSIX allowes `close(fd)` to return `EINTR` when the fd is already closed
    if errno == EINTR {
        return Ok(());
    }

    // NOTE: In POSIX systems, kernel may report delayed io failures on `close`,
    // this are fatal errors, and can not be retried
    //
    // We protect this by enforcing hard durability right after write ops, so the
    // occurrence of this error is an implementation failure
    if errno == EIO {
        return new_err(err::HCF, err_msg);
    }

    new_err(err::UNK, err_msg)
}

#[cfg(target_os = "linux")]
unsafe fn fdatasync_raw(fd: TFileId) -> FrozenRes<()> {
    let mut retries = 0; // only for EIO & EINTR errors
    loop {
        if hints::likely(libc::fdatasync(fd) == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // invalid fd or lack of support for sync
            EINVAL | EBADF => return new_err(err::HCF, err_msg),

            // read-only file (can also be caused by TOCTOU)
            EROFS => return new_err(err::PRM, err_msg),

            // fatal error, i.e. no sync for writes in recent window/batch
            EIO => return new_err(err::SYN, err_msg),

            // IO interrupt or fatal error, i.e. no sync for writes in recent window/batch
            //
            // NOTE: this must be handled seperately, cuase, if this error occurs,
            // the storage system must act, mark recent writes as failed or notify users,
            // etc. to keep the system robust and fault tolerent!
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_err(err::SYN, err_msg);
            }

            _ => return new_err(err::UNK, err_msg),
        }
    }
}

#[cfg(target_os = "macos")]
unsafe fn f_fullsync_raw(fd: TFileId) -> FrozenRes<()> {
    let mut retries = 0; // only for EINTR errors
    loop {
        if hints::likely(libc::fcntl(fd, libc::F_FULLFSYNC) == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_err(err::SYN, err_msg);
            }

            // lack of support for `F_FULLSYNC`
            libc::ENOTSUP | EOPNOTSUPP => break,

            // invalid fd or bad impl
            EINVAL | EBADF => return new_err(err::HCF, err_msg),

            // read-only file (can also be caused by TOCTOU)
            EROFS => return new_err(err::PRM, err_msg),

            // fatal error, i.e. no sync for writes in recent window/batch
            EIO => return new_err(err::SYN, err_msg),

            _ => return new_err(err::UNK, err_msg),
        }
    }

    // NOTE: when the storage device or fs, does not support fullsync, we fallback to `fsync()`,
    // which does not guaranty durability for sudden crash or power loss, which is acceptable when
    // strong durability is simply not available or allowed
    fsync_raw(fd)
}

/// Syncs in cache data updates on the storage device
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases no progress is
/// guaranteed, so the syscall must be retried
unsafe fn fsync_raw(fd: TFileId) -> FrozenRes<()> {
    let mut retries = 0; // only for EINTR errors
    loop {
        if hints::unlikely(libc::fsync(fd) != 0) {
            let errno = last_errno();
            let err_msg = err_msg(errno);

            match errno {
                // IO interrupt
                EINTR => {
                    if retries < MAX_RETRIES {
                        retries += 1;
                        continue;
                    }

                    // NOTE: sync error indicates that retries exhausted and durability is broken
                    // in the current/last window/batch
                    return new_err(err::SYN, err_msg);
                }

                // invalid fd or lack of support for sync
                EBADF | EINVAL => return new_err(err::HCF, err_msg),

                // read-only file (can also be caused by TOCTOU)
                EROFS => return new_err(err::PRM, err_msg),

                // fatal error, i.e. no sync for writes in recent window/batch
                EIO => return new_err(err::SYN, err_msg),

                _ => return new_err(err::UNK, err_msg),
            }
        }

        return Ok(());
    }
}

#[cfg(target_os = "linux")]
unsafe fn sync_file_range_raw(fd: TFileId, offset: usize, len: usize) -> FrozenRes<()> {
    let flag = libc::SYNC_FILE_RANGE_WRITE;
    let mut retries = 0; // only for EINTR errors

    loop {
        let res = libc::sync_file_range(fd, offset as off_t, len as off_t, flag);
        if hints::likely(res == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                // NOTE: sync error indicates that retries exhausted and durability is broken
                // in the current/last window/batch
                return new_err(err::SYN, err_msg);
            }

            // invalid fd or lack of support for sync
            EBADF | EINVAL => return new_err(err::HCF, err_msg),

            // read-only file (can also be caused by TOCTOU)
            EROFS => return new_err(err::PRM, err_msg),

            // fatal error, i.e. no sync for writes in recent window/batch
            EIO => return new_err(err::SYN, err_msg),

            // NOTE: on many fs mainly ones w/o local journaling, and older kernels does not support
            // `sync_file_range(SYNC_FILE_RANGE_WRITE)`, also as the use of this is only to hint the
            // fs (for perf gains for later sync), we simply let go of this and do not elivate any
            // kind of errors
            EOPNOTSUPP | libc::ENOSYS => return Ok(()),

            _ => return new_err(err::UNK, err_msg),
        }
    }
}

/// disk space preallocations using `fallocate()`
///
/// ## Semantics
///
/// This syscall does not change the size, nor the file capacity, the use is to attempt to reserve
/// disk blocks in advance to handle `ENOSPC` errors and to reduce letency for write ops to the [`POSIXFile`]
///
/// ## Support on fs
///
/// Not all kernel versions, fs (such as networked fs), support this syscall, in such cases, we simply
/// let go, and do not surface any errors, as this operation is mostly used as best-effort, and despite
/// the failure of `fallocate()`, the later `ftruncate()` would succeed, and the write ops also would
/// work all well, so we are good ;)
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases no progress is
/// guaranteed, so the syscall must be retried
#[cfg(target_os = "linux")]
unsafe fn fallocate_raw(fd: TFileId, curr_len: usize, len_to_add: usize) -> FrozenRes<()> {
    let mut retries = 0; // only for EINTR errors
    loop {
        if hints::likely(libc::fallocate(fd, 0, curr_len as off_t, len_to_add as off_t) == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                return new_err(err::GRW, err_msg);
            }

            // invalid fd
            EBADF | EINVAL => return new_err(err::HCF, err_msg),

            // read-only fs (can also be caused by TOCTOU)
            EROFS => return new_err(err::PRM, err_msg),

            // no space available on disk to grow
            ENOSPC => return new_err(err::NSP, err_msg),

            // NOTE: on many fs `fallocate()` may not be supported due to old kernel or fs
            // limitations, as use of this is only to hint the fs (for perf gains while
            // writes), we simply let go of this and do not elivate any kind of errors
            EOPNOTSUPP | libc::ENOSYS => return Ok(()),

            _ => return new_err(err::UNK, err_msg),
        }
    }
}

/// sets the size of [`POSIXFile`] to `len = curr_len + len_to_add` on fs
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases no progress is
/// guaranteed, so the syscall must be retried
unsafe fn ftruncate_raw(fd: TFileId, curr_len: usize, len_to_add: usize) -> FrozenRes<()> {
    let new_len = (curr_len + len_to_add) as off_t;
    let mut retries = 0; // only for EINTR errors

    loop {
        if hints::likely(ftruncate(fd, new_len) == 0) {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // IO interrupt
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                return new_err(err::GRW, err_msg);
            }

            // invalid fd or lack of support for sync
            EINVAL | EBADF => return new_err(err::HCF, err_msg),

            // read-only fs (can also be caused by TOCTOU)
            EROFS => return new_err(err::PRM, err_msg),

            // no space available on disk to grow
            ENOSPC => return new_err(err::NSP, err_msg),

            _ => return new_err(err::UNK, err_msg),
        }
    }
}

/// disk space (best-effort) preallocations using `F_PREALLOCATE`
///
/// ## Semantics
///
/// This syscall does not change the size, nor the file capacity, the use is to attempt to reserve
/// disk blocks in advance to letency during write ops to the [`POSIXFile`]
///
/// ## Support on fs
///
/// On many fs, `fcntl(F_PREALLOCATE)` may not be supported due to older kernels, or fs limitations
/// in such cases, we simply let go, and do not surface any errors, as this operation is mostly used as
/// best-effort, and despite the failure of `fcntl(F_PREALLOCATE)`, the later `ftruncate()` would succeed,
/// and the write ops also would work all well, so we are good ;)
///
/// ## Contiguous vs Non-contiguous Allocations
///
/// In `F_PREALLOCATE` calls, we get two allocation modes, contiguous and non-contiguous,
///
/// Calls w/ `F_ALLOCATECONTIG` are more likely to fail on fragmented fs, so we instantly fallback
/// to using `F_ALLOCATEALL` for reliability and correctness
///
/// ## Caveats (more like stupidity) of `F_ALLOCATEALL`
///
/// The preallocations may be revoked by fs due to (intentional) waker semantics, this acts more like a hint
/// and not a command to the fs, so the perf is not always guaranteed
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases no progress is
/// guaranteed, so the syscall must be retried
#[cfg(target_os = "macos")]
unsafe fn f_preallocate_raw(fd: TFileId, curr_len: usize, len_to_add: usize) -> FrozenRes<()> {
    let mut retries = 0; // only for EINTR errors

    // NOTE: by default we try w/ contiguous allocations for optimal perf, when not available,
    // i.e. received `ENOSPC`, we fallback to non-contiguous allocations
    let mut store = libc::fstore_t {
        fst_flags: libc::F_ALLOCATECONTIG,
        fst_posmode: libc::F_PEOFPOSMODE,
        fst_offset: curr_len as off_t,
        fst_length: len_to_add as off_t,
        fst_bytesalloc: 0,
    };

    loop {
        if libc::fcntl(fd, libc::F_PREALLOCATE, &store) == 0 {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                return new_err(err::GRW, err_msg);
            }

            // no space available on disk to grow
            ENOSPC => {
                // NOTE: we must retry w/ non-contiguous allocs for correctness, as sometimes
                // we do get `ENOSPC` only for contiguous allocs
                if store.fst_flags == libc::F_ALLOCATECONTIG {
                    store.fst_flags = libc::F_ALLOCATEALL;
                    retries = 0;
                    continue;
                }

                return new_err(err::NSP, err_msg);
            }

            // NOTE: on many fs `fcntl(F_PREALLOCATE)` may not be supported due to old kernel
            // or fs limitations, as use of this is only to hint the fs (for perf gains while
            // writes), we simply let go of this and do not elivate any kind of errors
            EOPNOTSUPP | libc::ENOTSUP => return Ok(()),

            // lack of support or weird fs behavior
            EINVAL => return Ok(()), // same reason as above to not elivate the error

            // invalid fd
            EBADF => return new_err(err::HCF, err_msg),

            // read-only fs
            EROFS => return new_err(err::PRM, err_msg),

            _ => return new_err(err::UNK, err_msg),
        }
    }
}

unsafe fn flock_raw(fd: TFileId) -> FrozenRes<()> {
    let mut retries = 0; // only for EINTR errors
    loop {
        if flock(fd, LOCK_EX | LOCK_NB) == 0 {
            return Ok(());
        }

        let errno = last_errno();
        let err_msg = err_msg(errno);

        match errno {
            // another process already holds the lock
            EWOULDBLOCK => {
                return new_err(err::LCK, err_msg);
            }

            // IO interrupt
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                return new_err(err::LCK, err_msg);
            }

            // invalid fd or lack of support
            EBADF | EINVAL => return new_err(err::HCF, err_msg),

            // os or fs, out of locks, i.e. lock exhaustion, may happen only on nfs
            ENOLCK => return new_err(err::LEX, err_msg),

            _ => return new_err(err::UNK, err_msg),
        }
    }
}

/// perform `fsync` for parent directory of file at given `path`
///
/// ## Purpose
///
/// In POSIX systems, syscalls like `open(path)`, `close(fd)` and `unlink(path)`, does not provide
/// crash safe durability, hence after a sudden crash or power loss, the operation may reverse,
/// resulting in catastrophic consequences
///
/// we must `fsync(parent_dir)`, for crash safe durability
unsafe fn sync_parent_dir(path: &std::path::Path) -> FrozenRes<()> {
    let parent = extract_parent_dir(path);
    let flags = O_RDONLY | O_DIRECTORY | O_CLOEXEC;
    let fd = open_raw(&parent, flags)?;

    #[cfg(target_os = "linux")]
    let res = fsync_raw(fd);

    #[cfg(target_os = "macos")]
    let res = f_fullsync_raw(fd);

    let _ = close_raw(fd);

    res
}

/// preps flags for `open()` syscall
///
/// ## Access Time Updates (O_NOATIME)
///
/// On linux, we can use the `O_NOATIME` flag to disable access time updates on the [`POSIXFile`]
///
/// Normally every I/O operation triggers an `atime` update for every write to disk, w/ use of
/// this flag, we try to eliminate counterproductive measures
///
/// ## Limitations of `O_NOATIME`
///
/// - not all fs support this flag, many silently ignore it, but some throw `EPERM` error
/// - It only works when the UID's are matched for calling processe and file owner
#[cfg(target_os = "linux")]
const fn prep_flags() -> c_int {
    O_RDWR | O_CLOEXEC | libc::O_NOATIME | O_CREAT
}

/// preps flags for `open()` syscall
#[cfg(target_os = "macos")]
const fn prep_flags() -> c_int {
    return O_RDWR | O_CLOEXEC | O_CREAT;
}

/// convert a `std::path::Path` into `std::ffu::CString`
fn path_to_cstring(path: &std::path::Path) -> FrozenRes<std::ffi::CString> {
    match std::ffi::CString::new(path.as_os_str().as_encoded_bytes()) {
        Ok(cs) => Ok(cs),
        Err(e) => new_err(err::INV, e),
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
unsafe fn err_msg(errno: i32) -> String {
    let ptr = strerror(errno);
    if ptr.is_null() {
        return String::new();
    }

    CStr::from_ptr(ptr).to_string_lossy().into_owned()
}

/// fetch max allowed `iovecs` per `preadv` & `pwritev` syscalls
fn read_max_iovecs() -> usize {
    *IOV_MAX_CACHE.get_or_init(|| unsafe {
        let res = sysconf(_SC_IOV_MAX);
        if res <= 0 {
            MAX_IOVECS
        } else {
            res as usize
        }
    })
}

fn extract_parent_dir(path: &std::path::Path) -> std::path::PathBuf {
    match path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p.to_path_buf(),
        _ => std::path::Path::new(".").to_path_buf(),
    }
}

/// Provide access pattern hint using `posix_fadvise(POSIX_FADV_RANDOM)`
///
/// ## Semantics
///
/// This syscall provides a hint to the kernel that the file will be accessed
/// in a random pattern. The kernel may disable read-ahead heuristics for the file.
///
/// ## Best-effort behavior
///
/// This call is purely advisory. If the kernel or filesystem does not support
/// the hint, we silently ignore the error and proceed.
///
/// ## Why do we retry?
///
/// POSIX syscalls are interruptible by signals, and may fail w/ `EINTR`, in such cases no progress is
/// guaranteed, so the syscall must be retried
#[inline]
#[cfg(target_os = "linux")]
unsafe fn f_advise_raw(fd: TFileId) -> FrozenRes<()> {
    let mut retries = 0;
    loop {
        let res = libc::posix_fadvise(fd, 0, 0, libc::POSIX_FADV_RANDOM);
        if res == 0 {
            return Ok(());
        }

        let err_msg = err_msg(res);
        match res {
            EINTR => {
                if retries < MAX_RETRIES {
                    retries += 1;
                    continue;
                }

                return new_err(err::UNK, err_msg);
            }

            // invalid fd
            EBADF | libc::ENOSYS | EINVAL => return new_err(err::HCF, err_msg),

            // as this is an best-effort call, we simply ignore if the call failed or advisory
            // hint is not supported
            _ => return Ok(()),
        }
    }
}

/// Builds a contiguous array of [`libc::iovec`] structures for vectored I/O
///
/// ## Stack vs Heap allocation
///
/// For small batches (`bufs.len() <= STACK_IOV`), the `iovec` array is allocated on the stack to avoid runtime
/// heap allocation overhead, and for larger batches, a `Vec<iovec>` is allocated on the heap
///
/// This design reduces allocator traffic & improves cache locality for common small batch workloads ;)
#[inline(always)]
unsafe fn build_iovecs(bufs: &[*mut u8], chunk_size: usize) -> (Vec<iovec>, Option<[iovec; STACK_IOV]>) {
    if bufs.len() <= STACK_IOV {
        let mut stack: mem::MaybeUninit<[iovec; STACK_IOV]> = mem::MaybeUninit::uninit();
        let ptr = stack.as_mut_ptr() as *mut iovec;

        for (i, &b) in bufs.iter().enumerate() {
            ptr.add(i).write(iovec {
                iov_base: b as *mut c_void,
                iov_len: chunk_size,
            });
        }

        let stack = stack.assume_init();
        (Vec::new(), Some(stack))
    } else {
        let mut heap = Vec::with_capacity(bufs.len());
        for &b in bufs {
            heap.push(iovec {
                iov_base: b as *mut c_void,
                iov_len: chunk_size,
            });
        }

        (heap, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn tmp_path() -> (tempfile::TempDir, PathBuf) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("tmp_file");

        (dir, path)
    }

    mod file_new_close {
        use super::*;

        #[test]
        fn ok_new_close_cycle() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();

                assert!(path.exists());
                file.close().unwrap();
            }
        }

        #[test]
        fn ok_new_close_cycle_on_existing() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file1 = POSIXFile::new(&path).unwrap();
                file1.close().unwrap();

                let file2 = POSIXFile::new(&path).unwrap();
                file2.close().unwrap();
            }
        }

        #[test]
        fn ok_close_on_close() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();

                file.close().unwrap();
                file.close().unwrap();
                file.close().unwrap();
            }
        }

        #[test]
        fn err_new_on_missing_parent_dir() {
            let (_dir, path) = tmp_path();

            unsafe {
                let missing = path.join("missing/file");
                let err = POSIXFile::new(&missing).unwrap_err();
                assert_eq!((err.id & 0xffff) as u16, err::INV.reason);
            }
        }
    }

    mod file_unlink {
        use super::*;

        #[test]
        fn ok_unlink_existing() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                assert!(path.exists());

                file.unlink(&path).unwrap();
                assert!(!path.exists());
            }
        }

        #[test]
        fn err_unlink_missing() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.unlink(&path).unwrap();

                let err = file.unlink(&path).unwrap_err();
                assert_eq!((err.id & 0xffff) as u16, err::INV.reason);
            }
        }
    }

    mod file_lock {
        use super::*;

        #[test]
        fn ok_flock_acquires_exclusive_lock() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.flock().unwrap(); // must succeed

                file.close().unwrap();
            }
        }

        #[test]
        fn err_flock_when_already_locked() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file1 = POSIXFile::new(&path).unwrap();
                file1.flock().unwrap();

                let file2 = POSIXFile::new(&path).unwrap();
                let err = file2.flock().unwrap_err();
                assert_eq!((err.id & 0xffff) as u16, err::LCK.reason);

                file1.close().unwrap();
                file2.close().unwrap();
            }
        }

        #[test]
        fn ok_flock_released_after_close() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file1 = POSIXFile::new(&path).unwrap();
                file1.flock().unwrap();
                file1.close().unwrap(); // releases lock

                let file2 = POSIXFile::new(&path).unwrap();
                file2.flock().unwrap(); // must succeed now

                file2.close().unwrap();
            }
        }
    }

    mod file_grow {
        use super::*;

        #[test]
        fn ok_grow() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();

                let initial = file.length().unwrap();
                assert_eq!(initial, 0);

                file.grow(0, 0x1000).unwrap();
                let new_len = file.length().unwrap();
                assert_eq!(new_len, 0x1000);

                let actual = file.length().unwrap();
                assert_eq!(actual, 0x1000);

                file.close().unwrap();
            }
        }

        #[test]
        fn ok_grow_extends_with_zero() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x500).unwrap();

                let mut buf = vec![0u8; 0x500];
                file.pread(buf.as_mut_ptr(), 0, 0x500).unwrap();

                assert!(buf.iter().all(|b| *b == 0));
                file.close().unwrap();
            }
        }
    }

    mod fil_sync {
        use super::*;

        #[test]
        fn ok_sync() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.sync().unwrap();
                file.close().unwrap();
            }
        }

        #[test]
        fn ok_sync_after_sync() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();

                file.sync().unwrap();
                file.sync().unwrap();
                file.sync().unwrap();
                file.sync().unwrap();

                file.close().unwrap();
            }
        }
    }

    mod write_read_single {
        use super::*;

        #[test]
        fn ok_pwrite_pread_cycle() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x200).unwrap();

                let mut data = b"grave_engine".to_vec();
                file.pwrite(data.as_mut_ptr(), 0x80, 0x0C).unwrap();

                let mut buf = vec![0u8; data.len()];
                file.pread(buf.as_mut_ptr(), 0x80, 0x0C).unwrap();
                assert_eq!(buf, data);
            }
        }

        #[test]
        fn ok_pwrite_pread_across_sessions() {
            let (_dir, path) = tmp_path();

            // new + write + close
            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x1000).unwrap();

                let mut data = b"persist_me".to_vec();
                file.pwrite(data.as_mut_ptr(), 0, data.len()).unwrap();

                file.sync().unwrap();
                file.close().unwrap();
            }

            // open + read + close
            unsafe {
                let file = POSIXFile::new(&path).unwrap();

                let mut buf = vec![0u8; 0x0A];
                file.pread(buf.as_mut_ptr(), 0, buf.len()).unwrap();
                assert_eq!(&buf, b"persist_me");
            }
        }

        #[test]
        fn ok_pwrite_concurrent_non_overlapping() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = std::sync::Arc::new(POSIXFile::new(&path).unwrap());
                file.grow(0, 0x2000).unwrap();

                let mut handles = vec![];
                for i in 0..0x0A {
                    let f = file.clone();
                    handles.push(std::thread::spawn(move || {
                        let mut data = vec![i as u8; 0x100];
                        f.pwrite(data.as_mut_ptr(), i * 0x100, data.len()).unwrap();
                    }));
                }

                for h in handles {
                    h.join().unwrap();
                }

                file.sync().unwrap();
                for i in 0..0x0A {
                    let mut buf = vec![0u8; 0x100];
                    file.pread(buf.as_mut_ptr(), i * 0x100, buf.len()).unwrap();
                    assert!(buf.iter().all(|b| *b == i as u8));
                }
            }
        }

        #[test]
        fn ok_pwrite_when_overlapping_last_wins() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x100).unwrap();

                let mut a = [1u8; 0x80];
                let mut b = [2u8; 0x80];

                file.pwrite(a.as_mut_ptr(), 0, a.len()).unwrap();
                file.pwrite(b.as_mut_ptr(), 0, b.len()).unwrap();

                let mut buf = vec![0u8; 0x80];
                file.pread(buf.as_mut_ptr(), 0, buf.len()).unwrap();
                assert!(buf.iter().all(|b| *b == 2));
            }
        }
    }

    mod write_read_vectored {
        use super::*;

        #[test]
        fn ok_pwritev_preadv_cycle() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x1000).unwrap();

                let mut buffers = [vec![1u8; 0x80], vec![2u8; 0x80], vec![3u8; 0x80]];
                let ptrs: Vec<*mut u8> = buffers.iter_mut().map(|b| b.as_mut_ptr()).collect();
                file.pwritev(&ptrs, 0, 0x80).unwrap();

                let mut read_bufs = [vec![0u8; 0x80], vec![0u8; 0x80], vec![0u8; 0x80]];
                let read_ptrs: Vec<*mut u8> = read_bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();
                file.preadv(&read_ptrs, 0, 0x80).unwrap();

                assert!(read_bufs[0].iter().all(|b| *b == 1));
                assert!(read_bufs[1].iter().all(|b| *b == 2));
                assert!(read_bufs[2].iter().all(|b| *b == 3));
            }
        }

        #[test]
        fn ok_pwritev_handles_large_iovec_batches() {
            let (_dir, path) = tmp_path();

            unsafe {
                let count = read_max_iovecs() + 5;

                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, count * 0x40).unwrap();

                let mut buffers: Vec<Vec<u8>> = (0..count).map(|i| vec![i as u8; 0x40]).collect();
                let ptrs: Vec<*mut u8> = buffers.iter_mut().map(|b| b.as_mut_ptr()).collect();

                file.pwritev(&ptrs, 0, 0x40).unwrap();
                file.sync().unwrap();

                for i in 0..count {
                    let mut buf = vec![0u8; 0x40];
                    file.pread(buf.as_mut_ptr(), i * 0x40, 0x40).unwrap();
                    assert!(buf.iter().all(|b| *b == i as u8));
                }
            }
        }

        #[test]
        fn ok_pwritev_preadv_across_sessions() {
            let (_dir, path) = tmp_path();

            // new + write + close
            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x400).unwrap();

                let mut bufs = [vec![9u8; 0x80], vec![8u8; 0x80]];
                let ptrs: Vec<*mut u8> = bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();

                file.pwritev(&ptrs, 0, 0x80).unwrap();
                file.sync().unwrap();
                file.close().unwrap();
            }

            // open + read + close
            unsafe {
                let file = POSIXFile::new(&path).unwrap();

                let mut read_bufs = [vec![0u8; 0x80], vec![0u8; 0x80]];
                let read_ptrs: Vec<*mut u8> = read_bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();
                file.preadv(&read_ptrs, 0, 0x80).unwrap();

                assert!(read_bufs[0].iter().all(|b| *b == 9));
                assert!(read_bufs[1].iter().all(|b| *b == 8));
            }
        }

        #[test]
        fn ok_pwritev_concurrent_non_overlapping() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = std::sync::Arc::new(POSIXFile::new(&path).unwrap());

                let threads = 8usize;
                let page = 0x80usize;
                let per_thread_iovs = 4usize;

                let total = threads * per_thread_iovs * page;
                file.grow(0, total).unwrap();

                let mut handles = Vec::new();
                for t in 0..threads {
                    let f = file.clone();

                    handles.push(std::thread::spawn(move || {
                        let mut bufs: Vec<Vec<u8>> =
                            (0..per_thread_iovs).map(|i| vec![(t * 10 + i) as u8; page]).collect();
                        let ptrs: Vec<*mut u8> = bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();

                        let offset = t * per_thread_iovs * page;
                        f.pwritev(&ptrs, offset, page).unwrap();
                    }));
                }

                for h in handles {
                    h.join().unwrap();
                }

                file.sync().unwrap();

                for t in 0..threads {
                    for i in 0..per_thread_iovs {
                        let mut buf = vec![0u8; page];
                        let offset = (t * per_thread_iovs + i) * page;
                        file.pread(buf.as_mut_ptr(), offset, page).unwrap();

                        let expected = (t * 10 + i) as u8;
                        assert!(buf.iter().all(|b| *b == expected));
                    }
                }
            }
        }
    }

    mod write_read_vectored_load {
        use super::*;

        #[test]
        fn ok_single_thread_large_batch() {
            let (_dir, path) = tmp_path();

            unsafe {
                let count = read_max_iovecs() * 3 + 17; // force multiple internal loops
                let page = 0x40usize;

                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, count * page).unwrap();

                let mut buffers: Vec<Vec<u8>> = (0..count).map(|i| vec![(i % 0xFB) as u8; page]).collect();
                let ptrs: Vec<*mut u8> = buffers.iter_mut().map(|b| b.as_mut_ptr()).collect();

                file.pwritev(&ptrs, 0, page).unwrap();
                file.sync().unwrap();

                let mut read_bufs: Vec<Vec<u8>> = (0..count).map(|_| vec![0u8; page]).collect();
                let read_ptrs: Vec<*mut u8> = read_bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();

                file.preadv(&read_ptrs, 0, page).unwrap();
                for (i, item) in read_bufs.iter().enumerate().take(count) {
                    let expected = (i % 0xFB) as u8;
                    assert!(item.iter().all(|b| *b == expected));
                }
            }
        }

        #[test]
        fn ok_multi_thread_large_batch() {
            let (_dir, path) = tmp_path();

            unsafe {
                let threads = 6usize;
                let page = 0x40usize;

                let per_thread = read_max_iovecs() * 2 + 0x0B;
                let total_pages = threads * per_thread;

                let file = std::sync::Arc::new(POSIXFile::new(&path).unwrap());
                file.grow(0, total_pages * page).unwrap();

                let mut handles = Vec::new();
                for t in 0..threads {
                    let f = file.clone();

                    handles.push(std::thread::spawn(move || {
                        let mut bufs: Vec<Vec<u8>> =
                            (0..per_thread).map(|i| vec![(t * 0x1F + i) as u8; page]).collect();
                        let ptrs: Vec<*mut u8> = bufs.iter_mut().map(|b| b.as_mut_ptr()).collect();

                        let offset = t * per_thread * page;
                        f.pwritev(&ptrs, offset, page).unwrap();
                    }));
                }

                for h in handles {
                    h.join().unwrap();
                }

                file.sync().unwrap();

                for t in 0..threads {
                    for i in 0..per_thread {
                        let mut buf = vec![0u8; page];
                        let offset = (t * per_thread + i) * page;
                        file.pread(buf.as_mut_ptr(), offset, page).unwrap();

                        let expected = (t * 0x1F + i) as u8;
                        assert!(buf.iter().all(|b| *b == expected));
                    }
                }
            }
        }
    }

    mod utils {
        use super::*;
        use std::{ffi::CString, os::unix::ffi::OsStrExt};

        #[test]
        fn ok_extract_parent_dir() {
            let cases = [
                ("/", "."),
                ("file.db", "."),
                ("./a/b/c.log", "./a/b"),
                ("data/file.db", "data"),
                ("/var/lib/grave/", "/var/lib"),
                ("/tmp/grave/file.db", "/tmp/grave"),
            ];

            for (input, expected) in cases {
                let path = PathBuf::from(input);
                let parent = extract_parent_dir(&path);
                assert_eq!(parent, PathBuf::from(expected), "failed for input: {input}");
            }
        }

        #[test]
        fn ok_path_to_cstring() {
            let cases: &[(&[u8], bool)] = &[
                (b"", true),
                (b"file.db", true),
                (b"bad\0path.db", false),
                (b"relative/path.db", true),
                (b"/tmp/grave/file.db", true),
            ];

            for (bytes, should_ok) in cases {
                let path = PathBuf::from(std::ffi::OsStr::from_bytes(bytes));
                let res = path_to_cstring(&path);

                match (res, should_ok) {
                    (Ok(cs), true) => {
                        let expected = CString::new(*bytes).expect("valid test case must not contain interior NUL");
                        assert_eq!(cs.as_bytes(), expected.as_bytes(), "mismatch for input: {:?}", bytes);
                    }
                    (Err(_), false) => {}
                    (other, _) => {
                        panic!("unexpected result for input {:?}: {:?}", bytes, other);
                    }
                }
            }
        }

        #[test]
        fn ok_read_max_iovecs() {
            let first = read_max_iovecs();
            let second = read_max_iovecs();

            assert!(first > 0, "IOV_MAX must be positive");
            assert!(first >= MAX_IOVECS && second >= MAX_IOVECS);
            assert_eq!(first, second, "value must be cached and stable");
        }

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

    mod file_lifecycle {
        use super::*;

        #[test]
        fn err_length_after_closed() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.close().unwrap();

                let err = file.length().unwrap_err();
                assert_eq!((err.id & 0xffff) as u16, err::HCF.reason);
            }
        }

        #[test]
        fn err_pread_after_closed() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x100).unwrap();
                file.close().unwrap();

                let mut buf = vec![0u8; 8];
                let err = file.pread(buf.as_mut_ptr(), 0, buf.len()).unwrap_err();
                assert_eq!((err.id & 0xffff) as u16, err::HCF.reason);
            }
        }

        #[test]
        fn err_pwrite_after_closed() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x100).unwrap();
                file.close().unwrap();

                let mut data = b"dead".to_vec();
                let err = file.pwrite(data.as_mut_ptr(), 0, data.len()).unwrap_err();
                assert_eq!((err.id & 0xffff) as u16, err::HCF.reason);
            }
        }

        #[test]
        fn err_sync_after_closed() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.close().unwrap();

                let err = file.sync().unwrap_err();
                assert_eq!((err.id & 0xffff) as u16, err::HCF.reason);
            }
        }

        #[test]
        fn err_grow_after_closed() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.close().unwrap();

                let err = file.grow(0, 0x100).unwrap_err();
                assert_eq!((err.id & 0xffff) as u16, err::HCF.reason);
            }
        }

        #[test]
        fn err_double_unlink_after_close() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();

                file.unlink(&path).unwrap();
                assert!(!path.exists());

                let err = file.unlink(&path).unwrap_err();
                assert_eq!((err.id & 0xffff) as u16, err::INV.reason);
            }
        }
    }

    mod raw_syscalls {
        use super::*;

        #[test]
        fn ok_sync_cycle() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x400).unwrap();

                let mut data = [7u8; 0x80];
                file.pwrite(data.as_mut_ptr(), 0, data.len()).unwrap();
                file.sync().unwrap(); // validates fdatasync or f_fullsync path

                let mut buf = vec![0u8; 0x80];
                file.pread(buf.as_mut_ptr(), 0, buf.len()).unwrap();
                assert_eq!(buf, data);
            }
        }

        #[cfg(target_os = "linux")]
        #[test]
        fn ok_sync_range() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x1000).unwrap();

                let mut data = [5u8; 0x100];
                file.pwrite(data.as_mut_ptr(), 0x200, data.len()).unwrap();

                // best-effort flush hint (must not fail when not supported by fs)
                file.sync_range(0x200, 0x100).unwrap();
                file.sync().unwrap();

                let mut buf = vec![0u8; 0x100];
                file.pread(buf.as_mut_ptr(), 0x200, buf.len()).unwrap();
                assert_eq!(buf, data);
            }
        }

        #[test]
        fn ok_write_read_at_eof_boundary() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                file.grow(0, 0x200).unwrap();

                let mut data = [3u8; 0x40];
                file.pwrite(data.as_mut_ptr(), 0x200 - 0x40, data.len()).unwrap();

                let mut buf = vec![0u8; 0x40];
                file.pread(buf.as_mut_ptr(), 0x200 - 0x40, buf.len()).unwrap();
                assert_eq!(buf, data);
            }
        }

        #[test]
        fn ok_multiple_open_close_cycles() {
            let (_dir, path) = tmp_path();

            unsafe {
                for _ in 0..0x0A {
                    let file = POSIXFile::new(&path).unwrap();
                    file.sync().unwrap();
                    file.close().unwrap();
                }
            }
        }

        #[test]
        #[cfg(target_os = "linux")]
        fn ok_f_advice_random() {
            let (_dir, path) = tmp_path();

            unsafe {
                let file = POSIXFile::new(&path).unwrap();
                f_advise_raw(file.fd()).unwrap();
            }
        }
    }
}
