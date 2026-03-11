//! Lock-free buffer pool used for staging IO buffers
//!
//! ## Features
//!
//! - *RAII Safe*
//! - *Graceful Shutdown*
//! - *Lock-free fast path*
//!
//! ## Polling
//!
//! The use of [`BufPool::allocate`] guarantees that the requested number of chunks are allocatated and stored
//! in [`Allocation`], but if the choosen `backend` is [`BPBackend::Prealloc`], the call blocks internally
//! when not enough chunks are available, generally till the previous [`Allocation`] are dropped
//!
//! ## Example
//!
//! ```
//! use frozen_core::bpool::{BufPool, BPCfg, BPBackend};
//!
//! let pool = BufPool::new(BPCfg {
//!     mid: 0,
//!     chunk_size: 0x20,
//!     backend: BPBackend::Prealloc { capacity: 4 },
//! });
//!
//! {
//!     let alloc = pool.allocate(4).unwrap();
//!     assert_eq!(alloc.count, 4);
//!     // `alloc` is dropped here
//! }
//!
//! let alloc2 = pool.allocate(4).unwrap();
//! assert_eq!(alloc2.count, 4);
//! ```

use crate::error::{FrozenErr, FrozenRes};
use std::{
    ptr,
    sync::{self, atomic},
};

const INVALID_POOL_SLOT: usize = u32::MAX as usize;

/// Config for [`BufPool`]
#[derive(Debug, Clone)]
pub struct BPCfg {
    /// Module id used for error logging
    pub mid: u8,

    /// Size (in bytes) of a single unit (chunk of memory) returned via [`Allocation`]
    pub chunk_size: usize,

    /// Backend used for allocations
    pub backend: BPBackend,
}

/// Available allocation backends for [`BufPool`]
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum BPBackend {
    /// All slots are dynamically constructed at runtime, avoids waiting for slot availablity under high contention
    /// at cost of runtime allocations
    ///
    /// ## When to use
    ///
    /// - burst workloads
    /// - low-contention code paths
    /// - requests that may exceed the configured pool capacity
    Dynamic,

    /// Uses a pre-allocated freelist w/ the given `capacity`
    ///
    /// All the chunks are allocated upfront, avoiding runtime allocations, while providing lower and more
    /// predicatble latency compared to [`BPBackend::Dynamic`]
    ///
    /// ## When to use
    ///
    /// - hot IO paths
    /// - write pipelines
    /// - storage engines
    /// - workloads where allocation latency must remain stable
    ///
    /// If all buffers are currently in use, [`BufPool::allocate`] blocks until another [`Allocation`]
    /// is dropped and buffers return to the pool
    ///
    /// ## Fallback
    ///
    /// For [`BPBackend::Prealloc`] backend, f `n` exceeds the pool capacity, the allocation is performed using the
    /// [`BPBackend::Dynamic`]
    Prealloc {
        /// Number of chunks to pre-allocate in memory
        capacity: usize,
    },
}

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
/// Bufs are allocated in batches using [`BufPool::allocate`], it may allocate fewer than requested, in such cases
/// caller should wait using [`BufPool::wait`] which block till any bufs are available to use again
#[derive(Debug)]
pub struct BufPool {
    cfg: BPCfg,
    state: BackendState,
    lock: sync::Mutex<()>,
    wait_cv: sync::Condvar,
    close_cv: sync::Condvar,
    active: atomic::AtomicUsize,
}

unsafe impl Send for BufPool {}
unsafe impl Sync for BufPool {}

impl BufPool {
    /// Create a new [`BufPool`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::bpool::{BufPool, BPCfg, BPBackend};
    ///
    /// let pool = BufPool::new(BPCfg {
    ///     mid: 0,
    ///     chunk_size: 0x20,
    ///     backend: BPBackend::Prealloc { capacity: 0x10 },
    /// });
    ///
    /// let alloc = pool.allocate(4).unwrap();
    /// assert_eq!(alloc.count, 4);
    /// ```
    pub fn new(cfg: BPCfg) -> Self {
        let state = BackendState::new(&cfg);
        Self {
            cfg,
            state,
            lock: sync::Mutex::new(()),
            wait_cv: sync::Condvar::new(),
            close_cv: sync::Condvar::new(),
            active: atomic::AtomicUsize::new(0),
        }
    }

    /// Allocate `n` buffers
    ///
    /// ## Blocking
    ///
    /// For [`BPBackend::Prealloc`] backend, if the pool does not currently contain enough chunks, call is blocked
    /// until all required chunks are allocated
    ///
    /// ## Fallback to [`BPBackend::Dynamic`]
    ///
    /// For [`BPBackend::Prealloc`] backend, f `n` exceeds the pool capacity, the allocation is performed using the
    /// [`BPBackend::Dynamic`]
    ///
    /// ## RAII
    ///
    /// The [`Allocation`] is RAII safe, as the allocated buffers are automatically reused (or free'ed from memory w/
    /// respect to the backend used) as the caller drops reference to the [`Allocation`]
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::bpool::{BufPool, BPCfg, BPBackend};
    ///
    /// let pool = BufPool::new(BPCfg {
    ///     mid: 0,
    ///     chunk_size: 0x20,
    ///     backend: BPBackend::Prealloc { capacity: 0x10 },
    /// });
    ///
    /// let alloc = pool.allocate(2).unwrap();
    /// assert_eq!(alloc.count, 2);
    /// assert_eq!(alloc.slots().len(), 2);
    /// ```
    #[inline(always)]
    pub fn allocate(&self, n: usize) -> FrozenRes<Allocation> {
        match &self.state {
            BackendState::Dynamic => Ok(Allocation::new_dynamic(self, n)),
            BackendState::Prealloc(state) => {
                if n > state.capacity {
                    return Ok(Allocation::new_dynamic(self, n));
                }

                state.allocate(n, self)
            }
        }
    }
}

impl Drop for BufPool {
    fn drop(&mut self) {
        let mut guard = match self.lock.lock() {
            Ok(g) => g,
            Err(_) => return,
        };

        while self.active.load(atomic::Ordering::Acquire) != 0 {
            guard = self.close_cv.wait(guard).expect("shutdown cv poisoned");
        }

        if let BackendState::Prealloc(state) = &self.state {
            let pool_size = state.capacity * self.cfg.chunk_size;

            // NOTE: We re-construct original allocation from the stored pointer! This builds up the vecotor
            // as it was created, which than is dropped by Rust destructor's automatically!
            let _ = unsafe { Vec::from_raw_parts(state.base_ptr, pool_size, pool_size) };
        }
    }
}

#[derive(Debug)]
enum BackendState {
    Dynamic,
    Prealloc(PreallocState),
}

impl BackendState {
    fn new(cfg: &BPCfg) -> Self {
        match cfg.backend {
            BPBackend::Dynamic => BackendState::Dynamic,
            BPBackend::Prealloc { capacity } => BackendState::Prealloc(PreallocState::new(capacity, cfg)),
        }
    }
}

#[derive(Debug)]
struct PreallocState {
    capacity: usize,
    base_ptr: TBPPtr,
    head: atomic::AtomicUsize,
    next: Box<[atomic::AtomicUsize]>,
}

impl PreallocState {
    fn new(capacity: usize, cfg: &BPCfg) -> Self {
        let pool_size = capacity * cfg.chunk_size;

        let mut pool = Vec::<u8>::with_capacity(pool_size);
        let base_ptr = pool.as_mut_ptr();

        // NOTE: `Vec::with_capacity(N)` allocates memory but keeps the len at 0, we use raw pointers to access
        // the slots, if the len stays at 0, it'd be UB while the reconstruction of the slice from the pointer
        // would be invalid as well
        unsafe { pool.set_len(pool_size) };

        // NOTE: Here, when `pool` goes out of scope, the `drop(pool)` will be called by the compiler, which
        // would drop the allocated memory, which for us must be pinned, to avoid this, we tell the compiler
        // to not call the drop, i.e. simply forget that the `pool` exists, while we also make sure to drop
        // this allocated memory pool manually when the [`BufPool`] itself is dropped
        std::mem::forget(pool);

        let mut next = Vec::with_capacity(capacity);
        for i in 0..capacity {
            let _i = 1 + i;
            let n = if _i < capacity { _i } else { INVALID_POOL_SLOT };
            next.push(atomic::AtomicUsize::new(n));
        }

        Self {
            capacity,
            base_ptr,
            next: next.into_boxed_slice(),
            head: atomic::AtomicUsize::new(pack_pool_idx(0, 0)),
        }
    }

    #[inline(always)]
    fn allocate(&self, n: usize, pool: &BufPool) -> FrozenRes<Allocation> {
        let mut remaining = n;
        let mut alloc = Allocation::new(pool, n);

        while remaining != 0 {
            let taken = self.alloc_batch(remaining, pool, &mut alloc);

            if taken == 0 {
                self.wait(pool)?;
                continue;
            }

            remaining -= taken;
        }

        Ok(alloc)
    }

    #[inline(always)]
    fn alloc_batch(&self, cap: usize, pool: &BufPool, out: &mut Allocation) -> usize {
        let mut head = self.head.load(atomic::Ordering::Relaxed);
        loop {
            let (idx, tag) = unpack_pool_idx(head);

            // NOTE:
            //
            // - If we reach the last entry (i.e. invalid ptr), we return early, despite not
            // allocating all the required buffers
            // - This allows caller to process allocated buffers, and avoid busy waiting for
            // more buffers
            // - The caller should poll to allocate, till all required bufs are allocated

            if idx == INVALID_POOL_SLOT {
                return 0;
            }

            //
            // local walk
            //

            let mut count = 1;
            let mut last = idx;

            while count < cap {
                let next = self.next[last].load(atomic::Ordering::Relaxed);
                if next == INVALID_POOL_SLOT {
                    break;
                }

                last = next;
                count += 1;
            }

            let new_head_idx = self.next[last].load(atomic::Ordering::Relaxed);
            let new_head = pack_pool_idx(new_head_idx, tag + 1);

            match self
                .head
                .compare_exchange(head, new_head, atomic::Ordering::AcqRel, atomic::Ordering::Acquire)
            {
                Err(h) => head = h,
                Ok(_) => {
                    let base = self.base_ptr;
                    let chunk = pool.cfg.chunk_size;

                    let slots = out.slots.slots();
                    slots.reserve(count);

                    let mut cur = idx;
                    for _ in 0..count {
                        slots.push(unsafe { base.add(cur * chunk) });
                        cur = self.next[cur].load(atomic::Ordering::Relaxed);
                    }

                    out.count += count;
                    return count;
                }
            }
        }
    }

    /// Block until at least one buffer becomes available
    ///
    /// This function is intended to be used when [`BufPool::allocate`] returns less than requested bufs,
    /// i.e. when pool is exhausted
    #[inline]
    fn wait(&self, pool: &BufPool) -> FrozenRes<()> {
        if self.has_free() {
            return Ok(());
        }

        let mut guard = pool
            .lock
            .lock()
            .map_err(|e| new_err_raw(BufPoolErrRes::Lpn, e, pool.cfg.mid))?;

        if self.has_free() {
            return Ok(());
        }

        while !self.has_free() {
            guard = pool
                .wait_cv
                .wait(guard)
                .map_err(|e| new_err_raw(BufPoolErrRes::Lpn, e, pool.cfg.mid))?;
        }

        Ok(())
    }

    #[inline]
    fn has_free(&self) -> bool {
        let (idx, _) = unpack_pool_idx(self.head.load(atomic::Ordering::Acquire));
        idx != INVALID_POOL_SLOT
    }

    #[inline(always)]
    fn free(&self, ptr: TBPPtr, pool: &BufPool) {
        let offset = unsafe { ptr.offset_from(self.base_ptr) } as usize;
        let idx = offset / pool.cfg.chunk_size;

        let mut head = self.head.load(atomic::Ordering::Acquire);
        loop {
            let (head_idx, head_tag) = unpack_pool_idx(head);
            self.next[idx].store(head_idx, atomic::Ordering::Relaxed);
            let new = pack_pool_idx(idx, 1 + head_tag);

            match self
                .head
                .compare_exchange(head, new, atomic::Ordering::AcqRel, atomic::Ordering::Acquire)
            {
                Ok(_) => {
                    pool.wait_cv.notify_one();
                    return;
                }
                Err(h) => head = h,
            }
        }
    }
}

/// Domain Id for [`BufPool`] is **19**
const ERRDOMAIN: u8 = 0x13;

/// Error codes for [`BufPool`]
#[repr(u16)]
pub enum BufPoolErrRes {
    /// (768) lock error (failed or poisoned)
    Lpn = 0x300,
}

impl BufPoolErrRes {
    #[inline]
    fn default_message(&self) -> &'static [u8] {
        match self {
            Self::Lpn => b"lock poisoned while waiting for BufPool",
        }
    }
}

#[inline]
fn new_err_raw<E: std::fmt::Display>(res: BufPoolErrRes, error: E, mid: u8) -> FrozenErr {
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
fn pack_pool_idx(idx: usize, tag: usize) -> usize {
    (tag << POOL_IDX_BITS) | (idx & POOL_IDX_MASK)
}

#[inline]
fn unpack_pool_idx(id: usize) -> (usize, usize) {
    (id & POOL_IDX_MASK, id >> POOL_IDX_BITS)
}

/// Pointer to buffer allocated by [`BufPool::allocate`]
pub type TBPPtr = *mut u8;

/// Buffer allocations allocated by [`BufPool::allocate`]
#[derive(Debug)]
pub struct Allocation {
    /// Number of buffers allocated, can be lower than the requested amount
    pub count: usize,

    /// Vector containing raw buffer pointers, i.e. [`BPPtr`]
    slots: AllocSlotType,

    /// Guard to enforce RAII safety
    guard: AllocationGuard,
}

unsafe impl Send for Allocation {}

impl Allocation {
    /// Returns the raw buffer pointers belonging to this allocation
    ///
    /// Each pointer references a contiguous memory region of size `BufPool::chunk_size`
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::bpool::{BufPool, BPCfg, BPBackend};
    ///
    /// let pool = BufPool::new(BPCfg {
    ///     mid: 0,
    ///     chunk_size: 0x20,
    ///     backend: BPBackend::Prealloc { capacity: 0x10 },
    /// });
    ///
    /// let alloc = pool.allocate(2).unwrap();
    ///
    /// for ptr in alloc.slots() {
    ///     assert!(!ptr.is_null());
    /// }
    /// ```
    #[inline]
    pub fn slots(&self) -> &Vec<TBPPtr> {
        match &self.slots {
            AllocSlotType::Pool(slots) => slots,
            AllocSlotType::Dynamic(slots) => slots,
        }
    }

    #[inline]
    fn new(pool: &BufPool, cap: usize) -> Self {
        pool.active.fetch_add(1, atomic::Ordering::Relaxed);

        Self {
            count: 0,
            guard: AllocationGuard(ptr::NonNull::from(pool)),
            slots: AllocSlotType::Pool(Vec::<TBPPtr>::with_capacity(cap)),
        }
    }

    #[inline]
    fn new_dynamic(pool: &BufPool, count: usize) -> Self {
        let total = pool.cfg.chunk_size * count;
        pool.active.fetch_add(1, atomic::Ordering::Relaxed);

        let mut slice = Vec::<u8>::with_capacity(total);
        let base_ptr = slice.as_mut_ptr();

        // NOTE: `Vec::with_capacity(N)` allocates memory but keeps the len at 0, we use raw pointers to access
        // the slots, if the len stays at 0, it'd be UB while the reconstruction of the slice from the pointer
        // would be invalid as well
        unsafe { slice.set_len(total) };

        // NOTE: Here, when `slice` goes out of scope, the `drop(allocation)` will be called by the compiler,
        // which would drop the allocated memory, which for us must be pinned, to avoid this, we tell the compiler
        // to not call the drop, i.e. simply forget that the `pool` exists, while we also make sure to drop
        // this allocated memory pool manually when the [`BufPool`] itself is dropped
        std::mem::forget(slice);

        let mut ptrs = Vec::with_capacity(count);
        for i in 0..count {
            let p = unsafe { base_ptr.add(i * pool.cfg.chunk_size) };
            ptrs.push(p);
        }

        Self {
            count,
            slots: AllocSlotType::Dynamic(ptrs),
            guard: AllocationGuard(ptr::NonNull::from(pool)),
        }
    }
}

impl Drop for Allocation {
    fn drop(&mut self) {
        let pool = unsafe { self.guard.0.as_ref() };

        match &self.slots {
            AllocSlotType::Pool(slots) => match &pool.state {
                BackendState::Prealloc(state) => {
                    for ptr in slots {
                        state.free(*ptr, pool);
                    }
                }

                // NOTE: The `AllocSlotType::Pool` can only originate from the `Prealloc` backend where chunks are
                // taken from the freelist, and when the backend is `Dynamic`, all allocations are created through
                // `Allocation::new_dynamic`, meaning no pool backed slots can ever exist
                _ => unreachable!(),
            },

            AllocSlotType::Dynamic(slots) => {
                // avoid panic in drop, i.e. UB risk (＠_＠;)
                if slots.is_empty() {
                    return;
                }

                let buf_size = pool.cfg.chunk_size;
                let total = buf_size * slots.len();
                let base = slots[0];

                let _ = unsafe { Vec::from_raw_parts(base, total, total) };
            }
        }
    }
}

#[derive(Debug)]
enum AllocSlotType {
    Pool(Vec<TBPPtr>),
    Dynamic(Vec<TBPPtr>),
}

impl AllocSlotType {
    fn slots(&mut self) -> &mut Vec<TBPPtr> {
        match self {
            Self::Pool(slots) => slots,
            Self::Dynamic(slots) => slots,
        }
    }
}

#[derive(Debug)]
struct AllocationGuard(ptr::NonNull<BufPool>);

impl Drop for AllocationGuard {
    fn drop(&mut self) {
        let pool = unsafe { self.0.as_ref() };

        if pool.active.fetch_sub(1, atomic::Ordering::Release) == 1 {
            // last user
            if let Ok(_g) = pool.lock.lock() {
                pool.close_cv.notify_one();
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

    fn new_pool_prealloc(capacity: usize) -> BufPool {
        BufPool::new(BPCfg {
            mid: TEST_MID,
            chunk_size: SIZE,
            backend: BPBackend::Prealloc { capacity },
        })
    }

    fn new_pool_dynamic() -> BufPool {
        BufPool::new(BPCfg {
            mid: TEST_MID,
            chunk_size: SIZE,
            backend: BPBackend::Dynamic,
        })
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

    mod pre_allocs {
        use super::*;

        #[test]
        fn ok_alloc_works() {
            let pool = new_pool_prealloc(CAP);
            let alloc = pool.allocate(1).unwrap();

            assert_eq!(alloc.count, 1);
            assert_eq!(alloc.slots().len(), 1);
        }

        #[test]
        fn ok_alloc_exact_cap_as_requested() {
            let pool = new_pool_prealloc(CAP);
            let alloc = pool.allocate(CAP).unwrap();

            assert_eq!(alloc.count, CAP);
            assert_eq!(alloc.slots().len(), CAP);
        }

        #[test]
        fn ok_alloc_all_even_when_exhausted() {
            let pool = new_pool_prealloc(CAP);

            let a1 = pool.allocate(CAP - 1).unwrap();
            assert_eq!(a1.count, CAP - 1);
            drop(a1);

            let a2 = pool.allocate(CAP).unwrap();
            assert_eq!(a2.count, CAP);
            drop(a2);

            let a3 = pool.allocate(1).unwrap();
            assert_eq!(a3.count, 1);
        }

        #[test]
        fn ok_alloc_all_when_requested_larger_then_cap() {
            let pool = new_pool_prealloc(CAP);

            let a1 = pool.allocate(CAP * 2).unwrap();
            assert_eq!(a1.count, CAP * 2);
        }

        #[test]
        fn ok_no_duplicate_slots_in_single_alloc() {
            let pool = new_pool_prealloc(CAP);

            let alloc = pool.allocate(CAP).unwrap();
            let mut ptrs: Vec<TBPPtr> = alloc.slots().iter().map(|s| *s).collect();

            // remove duplicates if any
            ptrs.sort();
            ptrs.dedup();

            assert_eq!(ptrs.len(), CAP);
        }

        #[test]
        fn ok_large_allocation_with_pre_alloc() {
            let pool = new_pool_prealloc(0x100);

            for i in 0..0x100 {
                let a = pool.allocate(i).unwrap();
                assert_eq!(a.slots().len(), i);
            }

            let final_alloc = pool.allocate(0x10).unwrap();
            assert_eq!(final_alloc.count, 0x10);
        }
    }

    mod dynamic_allocs {
        use super::*;

        #[test]
        fn ok_dynamic_alloc() {
            let pool = new_pool_dynamic();
            let alloc = pool.allocate(CAP).unwrap();

            assert_eq!(alloc.count, CAP);
            assert_eq!(alloc.slots().len(), CAP);
        }

        #[test]
        fn ok_no_duplicate_slots_in_single_dynamic_alloc() {
            let pool = new_pool_dynamic();

            let alloc = pool.allocate(CAP).unwrap();
            let mut ptrs: Vec<TBPPtr> = alloc.slots().iter().map(|s| *s).collect();

            // remove duplicates if any
            ptrs.sort();
            ptrs.dedup();

            assert_eq!(ptrs.len(), CAP);
        }

        #[test]
        fn ok_large_allocation_with_dynamic_alloc() {
            let pool = new_pool_dynamic();
            let alloc = pool.allocate(0x400).unwrap();

            assert_eq!(alloc.count, 0x400);
            assert_eq!(alloc.slots().len(), 0x400);
        }
    }

    mod raii_safety {
        use super::*;

        #[test]
        fn ok_pre_alloc_auto_free_on_drop() {
            let pool = new_pool_prealloc(CAP);

            {
                let alloc = pool.allocate(CAP).unwrap();
                assert_eq!(alloc.count, CAP);
            }

            // validate free on drop
            assert_eq!(pool.active.load(atomic::Ordering::Acquire), 0);

            let alloc2 = pool.allocate(CAP).unwrap();
            assert_eq!(alloc2.count, CAP);
        }

        #[test]
        fn ok_dynamic_alloc_auto_free_on_drop() {
            let pool = new_pool_dynamic();

            {
                let alloc = pool.allocate(CAP).unwrap();
                assert_eq!(alloc.count, CAP);
            }

            // validate free on drop
            assert_eq!(pool.active.load(atomic::Ordering::Acquire), 0);
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
            let pool = Arc::new(new_pool_prealloc(CAP * 0x0A));

            let mut handles = Vec::new();
            for _ in 0..THREADS {
                let pool = pool.clone();
                let barrier = barrier.clone();

                handles.push(thread::spawn(move || {
                    barrier.wait();

                    for _ in 0..ITERS {
                        let mut n = CAP / 2;
                        while n != 0 {
                            let alloc = pool.allocate(n).unwrap();
                            n -= alloc.count;
                        }
                    }
                }));
            }

            for h in handles {
                assert!(h.join().is_ok());
            }

            let final_alloc = pool.allocate(CAP).unwrap();
            assert_eq!(final_alloc.count, CAP);
        }

        #[test]
        fn ok_concurrent_dynamic_alloc() {
            const THREADS: usize = 8;
            const ITERS: usize = 0x200;

            let pool = Arc::new(new_pool_dynamic());

            let mut handles = Vec::new();
            for _ in 0..THREADS {
                let pool = pool.clone();

                handles.push(thread::spawn(move || {
                    for _ in 0..ITERS {
                        let alloc = pool.allocate(0x10).unwrap();
                        assert_eq!(alloc.count, 0x10);
                    }
                }));
            }

            for h in handles {
                assert!(h.join().is_ok());
            }

            assert_eq!(pool.active.load(atomic::Ordering::Acquire), 0);

            // pool should still function correctly
            let alloc = pool.allocate(CAP).unwrap();
            assert_eq!(alloc.count, CAP);
        }
    }

    mod polling {
        use super::*;
        use std::sync::Arc;
        use std::thread;
        use std::time::{Duration, Instant};

        #[test]
        fn ok_pre_alloc_blocks_until_buffers_freed() {
            let pool = Arc::new(new_pool_prealloc(1));
            let a = pool.allocate(1).unwrap();

            let pool2 = pool.clone();
            let h1 = thread::spawn(move || {
                let start = Instant::now();
                let alloc = pool2.allocate(1).expect("alloc failed");
                let elapsed = start.elapsed();

                assert!(elapsed >= Duration::from_millis(20));
                assert_eq!(alloc.count, 1);
            });

            let h2 = thread::spawn(move || {
                thread::sleep(Duration::from_millis(30));
                drop(a);
            });

            assert!(h1.join().is_ok());
            assert!(h2.join().is_ok());
        }
    }

    mod shutdown_safety {
        use super::*;
        use std::sync::Arc;

        #[test]
        fn drop_waits_for_active_pre_allocations() {
            let pool = Arc::new(new_pool_prealloc(CAP * 0x0A));
            let pool2 = pool.clone();

            let handle = std::thread::spawn(move || {
                let alloc = pool2.allocate(4).unwrap();
                std::thread::sleep(std::time::Duration::from_millis(0x32));
                drop(alloc);
            });

            std::thread::sleep(std::time::Duration::from_millis(0x0A)); // give the other thread time to allocate
            drop(pool); // this must block until alloc is dropped

            assert!(handle.join().is_ok());
        }

        #[test]
        fn drop_waits_for_active_dynamic_allocations() {
            let pool = Arc::new(new_pool_prealloc(CAP * 0x0A));
            let pool2 = pool.clone();

            let handle = std::thread::spawn(move || {
                let alloc = pool2.allocate(4).unwrap();
                std::thread::sleep(std::time::Duration::from_millis(0x32));
                drop(alloc);
            });

            std::thread::sleep(std::time::Duration::from_millis(0x0A)); // give the other thread time to allocate
            drop(pool); // this must block until alloc is dropped

            assert!(handle.join().is_ok());
        }

        #[test]
        fn ok_cross_thread_drop() {
            let pool = Arc::new(new_pool_prealloc(0x0C));
            let alloc = pool.allocate(0x0C).unwrap();

            let h1 = {
                std::thread::spawn(move || {
                    drop(alloc);
                })
            };

            let h2 = {
                let pool = pool.clone();

                std::thread::spawn(move || {
                    let a = pool.allocate(8).unwrap();
                    assert_eq!(a.count, 8);
                })
            };

            assert!(h1.join().is_ok());
            assert!(h2.join().is_ok());
        }
    }
}
