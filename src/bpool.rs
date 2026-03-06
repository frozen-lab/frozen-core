//! Lock-free buffer pool used for staging IO buffers
//!
//! ## Features
//!
//! - *RAII Safe*
//! - *Graceful Shutdown*
//! - *Lock-free fast path*
//!
//! ## Pooling for allocations
//!
//! Bufs are allocated in batches using [`BPool::allocate`], it may allocate fewer than requested, in such cases
//! caller should wait using [`BPool::wait`] which block till any bufs are available to use again
//!
//! ## Example
//!
//! ```
//! use frozen_core::bpool::BPool;
//! use std::sync::Arc;
//! use std::thread;
//!
//! const MODULE_ID: u8 = 0;
//! const CAPACITY: usize = 8;
//! const BUF_SIZE: usize = 0x20;
//!
//! let pool = Arc::new(BPool::new(BUF_SIZE, CAPACITY, MODULE_ID));
//! let mut handles = Vec::new();
//!
//! for _ in 0..4 {
//!     let pool = pool.clone();
//!     handles.push(thread::spawn(move || {
//!         for _ in 0..0x80 {
//!             let mut n = 2;
//!             while n != 0 {
//!                 let alloc = pool.allocate(n);
//!
//!                 // pool when not all bufs are allocated
//!                 if alloc.count == 0 {
//!                     pool.wait().expect("wait failed");
//!                     continue;
//!                 }
//!
//!                n -= alloc.count;
//!             }
//!
//!             // NOTE: allocated bufs are freed automatically when `alloc` drops
//!         }
//!     }));
//! }
//!
//! for h in handles {
//!     h.join().unwrap();
//! }
//! ```

use crate::error::{FrozenErr, FrozenRes};
use std::sync::{self, atomic};

const INVALID_POOL_SLOT: usize = u32::MAX as usize;

/// Lock-free buffer pool used for staging IO buffers
///
/// ## Features
///
/// - *RAII Safe*
/// - *Graceful Shutdown*
/// - *Lock-free fast path*
///
/// ## Pooling for allocations
///
/// Bufs are allocated in batches using [`BPool::allocate`], it may allocate fewer than requested, in such cases
/// caller should wait using [`BPool::wait`] which block till any bufs are available to use again
///
/// ## Example
///
/// ```
/// const MODULE_ID: u8 = 0;
/// const CAPACITY: usize = 4;
/// const BUF_SIZE: usize = 0x20;
///
/// let pool = frozen_core::bpool::BPool::new(BUF_SIZE, CAPACITY, MODULE_ID);
///
/// {
///     // NOTE: allocations are RAII safe, hence the underlying resource is reused when `alloc` is dropped
///     let alloc = pool.allocate(4);
///     assert_eq!(alloc.count, 4);
/// }
///
/// let alloc2 = pool.allocate(4);
/// assert_eq!(alloc2.count, 4);
/// ```
#[derive(Debug)]
pub struct BPool {
    ptr: PoolPtr,
    module_id: u8,
    capacity: usize,
    buf_size: usize,
    lock: sync::Mutex<()>,
    wait_cv: sync::Condvar,
    close_cv: sync::Condvar,
    head: atomic::AtomicUsize,
    active: atomic::AtomicUsize,
    next: Box<[atomic::AtomicUsize]>,
}

unsafe impl Send for BPool {}
unsafe impl Sync for BPool {}

impl BPool {
    /// Create a new instance of [`BPool`]
    ///
    /// ## Params
    ///
    /// - `buf_size`: size of each buf in [`BPool`]
    /// - `capacity`: capacity of [`BPool`] i.e. number of buffers in memory
    /// - `module_id`: id used by [`FrozenErr`] for error propagation
    ///
    /// ## Example
    ///
    /// ```
    /// const MODULE_ID: u8 = 0;
    /// const CAPACITY: usize = 4;
    /// const BUF_SIZE: usize = 0x20;
    ///
    /// let pool = frozen_core::bpool::BPool::new(BUF_SIZE, CAPACITY, MODULE_ID);
    ///
    /// {
    ///     // NOTE: allocations are RAII safe, hence the underlying resource is reused when `alloc` is dropped
    ///     let alloc = pool.allocate(4);
    ///     assert_eq!(alloc.count, 4);
    /// }
    ///
    /// let alloc2 = pool.allocate(4);
    /// assert_eq!(alloc2.count, 4);
    /// ```
    pub fn new(buf_size: usize, capacity: usize, module_id: u8) -> Self {
        let pool_size = capacity * buf_size;
        let mut pool = Vec::<u8>::with_capacity(pool_size);
        let ptr = PoolPtr { ptr: pool.as_mut_ptr() };

        // NOTE: `Vec::with_capacity(N)` allocates memory but keeps the len at 0. We use raw pointers
        // to access different slots, if the len stays at 0, it'd create undefined behavior. Also, the
        // reconstruct of vector from the pointer would become invalid. To avoid memory leaks, we
        // reconstruct the vec from the pointer in the drop.
        unsafe { pool.set_len(pool_size) };

        // NOTE: When the `pool` is dropped, it'll free up the entire memory. This should not happen,
        // as we own the underlying memory via mutable pointer, which is an implicit owenership, so we
        // avoid destruction of `pool` when it goes out of scope.
        std::mem::forget(pool);

        let mut next = Vec::with_capacity(capacity);
        for i in 0..capacity {
            let _i = 1 + i;
            let n = if _i < capacity { _i } else { INVALID_POOL_SLOT };
            next.push(atomic::AtomicUsize::new(n));
        }

        Self {
            ptr,
            capacity,
            buf_size,
            module_id,
            wait_cv: sync::Condvar::new(),
            close_cv: sync::Condvar::new(),
            lock: sync::Mutex::new(()),
            next: next.into_boxed_slice(),
            active: atomic::AtomicUsize::new(0),
            head: atomic::AtomicUsize::new(pack_pool_idx(0, 0)),
        }
    }

    /// Allocates `N` buffers for staging IO ops
    ///
    /// ## Calling Pattern
    ///
    /// ```txt
    /// remaining = n
    /// loop
    ///     alloc = allocate(remaining)
    ///     if alloc.count == 0
    ///         wait()
    ///         continue
    ///
    ///     remaining -= alloc.count
    ///     if remaining == 0
    ///         break
    /// ```
    ///
    /// ## Polling
    ///
    /// This function may not allocate all the `N` required buffers in one call, so the caller must
    /// poll (wait and retry) for remaining `N` buffers
    ///
    /// ## RAII Safety
    ///
    /// All [`BPool`] aloocations are RAII safe by default, hence when the variable which stores the result
    /// of `allocate`, is dropped, the buffer's it holds are also automatically freed, the burden of _freeing after use_
    /// does not fall on the caller
    ///
    /// ## Example
    ///
    /// ```
    /// const MODULE_ID: u8 = 0;
    /// const CAPACITY: usize = 4;
    /// const BUF_SIZE: usize = 0x20;
    ///
    /// let pool = frozen_core::bpool::BPool::new(BUF_SIZE, CAPACITY, MODULE_ID);
    ///
    /// let alloc1 = pool.allocate(4);
    /// assert!(alloc1.count == 4);
    ///
    /// let alloc2 = pool.allocate(1);
    /// assert!(alloc2.count == 0);
    ///
    /// drop(alloc1);
    ///
    /// let alloc3 = pool.allocate(1);
    /// assert!(alloc3.count == 1);
    /// ```
    #[inline(always)]
    pub fn allocate(&self, n: usize) -> Allocation {
        let mut head = self.head.load(atomic::Ordering::Acquire);
        let mut batch = Allocation::new(self, n);

        loop {
            let (idx, tag) = unpack_pool_idx(head);

            // NOTE: If we reach the last entry (i.e. invalid ptr), we return early, despite not
            // allocating all the required buffers
            //
            // This allows caller to process allocated buffers, and avoid busy waiting for
            // more buffers
            //
            // The caller should pool to allocate, till all the required buffers are allocated
            if idx == INVALID_POOL_SLOT {
                return batch;
            }

            //
            // local walk
            //

            let mut count = 1;
            let mut last = idx;

            while count < n {
                // This is valid as `next` is already the index (unpacked version) of the slot
                let next = self.next[last as usize].load(atomic::Ordering::Relaxed);
                if next == INVALID_POOL_SLOT {
                    break;
                }

                last = next;
                count += 1;
            }

            let new_head_idx = self.next[last as usize].load(atomic::Ordering::Relaxed);
            let new_head = pack_pool_idx(new_head_idx, 1 + tag);

            match self
                .head
                .compare_exchange(head, new_head, atomic::Ordering::AcqRel, atomic::Ordering::Acquire)
            {
                Err(h) => head = h,
                Ok(_) => {
                    let mut cur = idx;
                    for _ in 0..count {
                        batch.slots.push(self.ptr.add((cur * self.buf_size) as u64));
                        cur = self.next[cur as usize].load(atomic::Ordering::Relaxed);
                    }

                    batch.count = count;
                    return batch;
                }
            }
        }
    }

    #[inline(always)]
    fn free(&self, ptr: &PoolPtr) {
        let offset = self.ptr.offset_from(&ptr);
        let idx = offset / self.buf_size;

        let mut head = self.head.load(atomic::Ordering::Acquire);
        loop {
            let (head_idx, head_tag) = unpack_pool_idx(head);
            self.next[idx as usize].store(head_idx, atomic::Ordering::Relaxed);
            let new = pack_pool_idx(idx, 1 + head_tag);

            match self
                .head
                .compare_exchange(head, new, atomic::Ordering::AcqRel, atomic::Ordering::Acquire)
            {
                Ok(_) => {
                    self.wait_cv.notify_one();
                    return;
                }
                Err(h) => head = h,
            }
        }
    }

    /// Block until at least one buffer becomes available
    ///
    /// This function is intended to be used when [`BPool::allocate`] returns less than requested bufs,
    /// i.e. when pool is exhausted
    ///
    /// ## Polling
    ///
    /// The typical allocation pattern is,
    ///
    /// - Attempt allocation w/ [`BPool::allocate`]
    /// - If less than requested bufs are allocated, call [`BPool::wait`]
    /// - Retry the allocation; all within a loop
    ///
    /// ## Notes
    ///
    /// - The caller must retry [`BPool::allocate`] after calling [`BPool::wait`]
    /// - Only threads waiting for buffers are blocked, the allocation fast path remains lock-free
    ///
    /// ## Example
    ///
    /// ```
    /// const MODULE_ID: u8 = 0;
    /// const CAPACITY: usize = 2;
    /// const BUF_SIZE: usize = 0x20;
    ///
    /// let pool = frozen_core::bpool::BPool::new(BUF_SIZE, CAPACITY, MODULE_ID);
    ///
    /// let alloc = pool.allocate(2);
    /// assert_eq!(alloc.count, 2);
    ///
    /// let empty = pool.allocate(1);
    /// assert_eq!(empty.count, 0);
    ///
    /// drop(alloc);
    /// pool.wait().expect("wait failed");
    ///
    /// let alloc2 = pool.allocate(1);
    /// assert_eq!(alloc2.count, 1);
    /// ```
    #[inline]
    pub fn wait(&self) -> FrozenRes<()> {
        if self.has_free() {
            return Ok(());
        }

        let mut guard = self
            .lock
            .lock()
            .map_err(|e| new_err_raw(BPoolErrRes::Lpn, e, self.module_id))?;

        if self.has_free() {
            return Ok(());
        }

        while !self.has_free() {
            guard = self
                .wait_cv
                .wait(guard)
                .map_err(|e| new_err_raw(BPoolErrRes::Lpn, e, self.module_id))?;
        }

        Ok(())
    }

    #[inline]
    fn has_free(&self) -> bool {
        let (idx, _) = unpack_pool_idx(self.head.load(atomic::Ordering::Acquire));
        idx != INVALID_POOL_SLOT
    }
}

impl Drop for BPool {
    fn drop(&mut self) {
        let mut guard = match self.lock.lock() {
            Ok(g) => g,
            Err(_) => return,
        };

        while self.active.load(atomic::Ordering::Acquire) != 0 {
            guard = self.close_cv.wait(guard).expect("shutdown cv poisoned");
        }

        let pool_size = self.capacity * self.buf_size;

        // NOTE: We re-construct original allocation from the stored pointer! This builds up the vecotor
        // as it was created, which than is dropped by Rust destructor's automatically!
        let _ = unsafe { Vec::from_raw_parts(self.ptr.ptr, pool_size, pool_size) };
    }
}

/// Domain Id for [`BPool`] is **19**
const ERRDOMAIN: u8 = 0x13;

/// Error codes for [`BPool`]
#[repr(u16)]
pub enum BPoolErrRes {
    /// (518) lock error (failed or poisoned)
    Lpn = 0x301,
}

impl BPoolErrRes {
    #[inline]
    fn default_message(&self) -> &'static [u8] {
        match self {
            Self::Lpn => b"lock poisoned while waiting for BPool",
        }
    }
}

#[inline]
fn new_err_raw<E: std::fmt::Display>(res: BPoolErrRes, error: E, mid: u8) -> FrozenErr {
    let detail = res.default_message();
    FrozenErr::new(
        mid,
        ERRDOMAIN,
        res as u16,
        detail,
        error.to_string().as_bytes().to_vec(),
    )
}

const POOL_IDX_BITS: usize = 0x20;
const POOL_IDX_MASK: usize = (1 << POOL_IDX_BITS) - 1;

#[inline]
const fn pack_pool_idx(idx: usize, tag: usize) -> usize {
    (tag << POOL_IDX_BITS) | (idx & POOL_IDX_MASK)
}

#[inline]
const fn unpack_pool_idx(id: usize) -> (usize, usize) {
    (id & POOL_IDX_MASK, id >> POOL_IDX_BITS)
}

type TPoolPtr = *mut u8;

/// Pointer to buffer allocated by [`BPool::allocate`]
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct PoolPtr {
    /// Raw pointer to the start of a buffer owned by the pool, where the valid memory range is `[ptr, ptr + buf_size)`
    pub ptr: TPoolPtr,
}

unsafe impl Send for PoolPtr {}
unsafe impl Sync for PoolPtr {}

impl PoolPtr {
    #[inline]
    fn add(&self, count: u64) -> Self {
        Self {
            ptr: unsafe { self.ptr.add(count as usize) },
        }
    }

    #[inline]
    fn offset_from(&self, ptr: &Self) -> usize {
        unsafe { ptr.ptr.offset_from(self.ptr) as usize }
    }
}

/// Buffer allocations allocated by [`BPool::allocate`]
#[derive(Debug)]
pub struct Allocation<'a> {
    /// Number of buffers allocated, can be lower than the requested amount
    pub count: usize,

    /// Vector of [`PoolPtr`] objects, i.e. Raw buffer pointers
    pub slots: Vec<PoolPtr>,

    /// Guard to enforce RAII safety
    guard: AllocationGuard<'a>,
}

impl<'a> Allocation<'a> {
    #[inline]
    fn new(pool: &'a BPool, cap: usize) -> Self {
        pool.active.fetch_add(1, atomic::Ordering::Relaxed);

        Self {
            count: 0,
            slots: Vec::<PoolPtr>::with_capacity(cap),
            guard: AllocationGuard(pool),
        }
    }
}

impl<'a> Drop for Allocation<'a> {
    fn drop(&mut self) {
        for ptr in &self.slots {
            self.guard.0.free(ptr);
        }
    }
}

#[derive(Debug)]
struct AllocationGuard<'a>(&'a BPool);

impl Drop for AllocationGuard<'_> {
    fn drop(&mut self) {
        if self.0.active.fetch_sub(1, atomic::Ordering::Release) == 1 {
            // last user
            if let Ok(_g) = self.0.lock.lock() {
                self.0.close_cv.notify_one();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::TEST_MID;

    const CAP: usize = 0x20;
    const SIZE: usize = 0x0A;

    fn new_pool() -> BPool {
        BPool::new(SIZE, CAP, TEST_MID)
    }

    mod utils {
        use super::*;

        #[test]
        fn pack_unpack_cycle() {
            let pack_id = pack_pool_idx(0x20, 0x0A);
            let (idx, tag) = unpack_pool_idx(pack_id);

            assert_eq!(idx, 0x20);
            assert_eq!(tag, 0x0A);
        }
    }

    mod allocations {
        use super::*;

        #[test]
        fn ok_alloc_works() {
            let pool = new_pool();
            let alloc = pool.allocate(1);

            assert_eq!(alloc.count, 1);
            assert_eq!(alloc.slots.len(), 1);
        }

        #[test]
        fn ok_alloc_exact_cap_as_requested() {
            let pool = new_pool();
            let alloc = pool.allocate(CAP);

            assert_eq!(alloc.count, CAP);
            assert_eq!(alloc.slots.len(), CAP);
        }

        #[test]
        fn ok_alloc_partial_when_exhausted() {
            let pool = new_pool();

            let a1 = pool.allocate(CAP - 1);
            assert_eq!(a1.count, CAP - 1);

            let a2 = pool.allocate(CAP);
            assert_eq!(a2.count, 1);

            let a3 = pool.allocate(1);
            assert_eq!(a3.count, 0);
        }

        #[test]
        fn ok_allocs_none_when_exhausted() {
            let pool = new_pool();

            let _a1 = pool.allocate(CAP);

            let a2 = pool.allocate(1);
            assert_eq!(a2.count, 0);
        }

        #[test]
        fn ok_no_duplicate_slots_in_single_alloc() {
            let pool = new_pool();

            let alloc = pool.allocate(CAP);
            let mut ptrs: Vec<_> = alloc.slots.iter().map(|s| s.ptr).collect();

            // remove duplicates if any
            ptrs.sort();
            ptrs.dedup();

            assert_eq!(ptrs.len(), CAP);
        }
    }

    mod raii_safety {
        use super::*;

        #[test]
        fn ok_auto_free_on_drop() {
            let pool = new_pool();

            {
                let alloc = pool.allocate(CAP);
                assert_eq!(alloc.count, CAP);
            }

            let alloc2 = pool.allocate(CAP);
            assert_eq!(alloc2.count, CAP);
        }
    }

    mod concurrency {
        use super::*;
        use std::sync::{Arc, Barrier};
        use std::thread;

        #[test]
        fn ok_concurrent_alloc() {
            const THREADS: usize = 8;
            const ITERS: usize = 0x1000;

            let barrier = Arc::new(Barrier::new(THREADS));
            let pool = Arc::new(BPool::new(SIZE, CAP * 0x0A, TEST_MID));

            let mut handles = Vec::new();
            for _ in 0..THREADS {
                let pool = pool.clone();
                let barrier = barrier.clone();

                handles.push(thread::spawn(move || {
                    barrier.wait();

                    for _ in 0..ITERS {
                        let mut n = CAP / 2;
                        while n != 0 {
                            let alloc = pool.allocate(n);
                            if alloc.count == 0 {
                                pool.wait().expect("wait for free");
                                continue;
                            }

                            n -= alloc.count;
                        }
                    }
                }));
            }

            for h in handles {
                assert!(h.join().is_ok());
            }

            let final_alloc = pool.allocate(CAP);
            assert_eq!(final_alloc.count, CAP);
        }
    }

    mod shutdown_safety {
        use super::*;
        use std::sync::Arc;

        #[test]
        fn drop_waits_for_active_allocations() {
            let pool = Arc::new(BPool::new(SIZE, CAP * 0x0A, TEST_MID));
            let pool2 = pool.clone();

            let handle = std::thread::spawn(move || {
                let alloc = pool2.allocate(4);
                std::thread::sleep(std::time::Duration::from_millis(50));
                drop(alloc);
            });

            // give the other thread time to allocate
            std::thread::sleep(std::time::Duration::from_millis(10));

            // this must block until alloc is dropped
            drop(pool);

            assert!(handle.join().is_ok());
        }
    }
}
