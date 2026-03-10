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
//! Bufs are allocated in batches using [`BufPool::allocate`], it may allocate fewer than requested, in such cases
//! caller should wait using [`BufPool::wait`] which block till any bufs are available to use again

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

unsafe impl Send for BPCfg {}
unsafe impl Sync for BPCfg {}

/// Available allocation backends for [`BufPool`]
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum BPBackend {
    /// All slots are dynamically constructed at runtime, avoids waiting for slot availablity under high contention
    /// at cost of runtime allocations
    Dynamic,

    /// Uses a pre-allocated freelist w/ the given `capacity`
    ///
    /// All the chunks are allocated upfront, avoiding runtime allocations, while providing lower and more
    /// predicatble latency compared to [`BPBackend::Dynamic`]
    ///
    /// If a request asks for more chunks then the `capacity`, [`BPBackend::Dynamic`] is used as a fallback
    ///
    /// ## Polling
    ///
    /// TODO: Add notes
    Prealloc {
        /// Bumber of chunks to pre-allocate in memory
        capacity: usize,
    },
}

unsafe impl Send for BPBackend {}
unsafe impl Sync for BPBackend {}

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

impl BufPool {
    /// Create a new instance of [`BufPool`]
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

    /// Allocates `n` chunks for staging IO ops
    ///
    /// ## RAII Safe
    ///
    /// The [`Allocation`] is RAII safe, as the allocated buffers are automatically reused or freed from memory w/
    /// respect to the backend used, as the caller drops reference to the [`Allocation`]
    #[inline]
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

        match &self.state {
            BackendState::Prealloc(state) => {
                let pool_size = state.capacity * self.cfg.chunk_size;

                // NOTE: We re-construct original allocation from the stored pointer! This builds up the vecotor
                // as it was created, which than is dropped by Rust destructor's automatically!
                let _ = unsafe { Vec::from_raw_parts(state.base_ptr.ptr, pool_size, pool_size) };
            }
            _ => {}
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
    base_ptr: BPPtr,
    head: atomic::AtomicUsize,
    next: Box<[atomic::AtomicUsize]>,
}

impl PreallocState {
    fn new(capacity: usize, cfg: &BPCfg) -> Self {
        let pool_size = capacity * cfg.chunk_size;

        let mut pool = Vec::<u8>::with_capacity(pool_size);
        let base_ptr = BPPtr { ptr: pool.as_mut_ptr() };

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
        let mut head = self.head.load(atomic::Ordering::Acquire);
        loop {
            let (idx, tag) = unpack_pool_idx(head);

            // NOTE: If we reach the last entry (i.e. invalid ptr), we return early, despite not
            // allocating all the required buffers
            //
            // This allows caller to process allocated buffers, and avoid busy waiting for
            // more buffers
            //
            // The caller should poll to allocate, till all required bufs are allocated
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
                    let mut cur = idx;
                    for _ in 0..count {
                        out.slots
                            .slots()
                            .push(self.base_ptr.add((cur * pool.cfg.chunk_size) as u64));

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
    ///
    /// ## Polling
    ///
    /// The typical allocation pattern is,
    ///
    /// - Attempt allocation w/ [`BufPool::allocate`]
    /// - If less than requested bufs are allocated, call [`BufPool::wait`]
    /// - Retry the allocation; all within a loop
    ///
    /// ## Notes
    ///
    /// - The caller must retry [`BufPool::allocate`] after calling [`BufPool::wait`]
    /// - Only threads waiting for buffers are blocked, the allocation fast path remains lock-free
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
    fn free(&self, ptr: &BPPtr, pool: &BufPool) {
        let offset = self.base_ptr.offset_from(ptr);
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

type TBPPtr = *mut u8;

/// Pointer to buffer allocated by [`BufPool::allocate`]
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct BPPtr {
    /// Raw pointer to the start of a buffer owned by the pool, where the valid memory range is `[ptr, ptr + buf_size)`
    pub ptr: TBPPtr,
}

unsafe impl Send for BPPtr {}

impl BPPtr {
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
    /// Get a referenced vector containing raw buffer pointers
    #[inline]
    pub fn slots(&self) -> &Vec<BPPtr> {
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
            slots: AllocSlotType::Pool(Vec::<BPPtr>::with_capacity(cap)),
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

        // NOTE: Here, when `slice` goes out of scope, the `drop(pool)` will be called by the compiler, which
        // would drop the allocated memory, which for us must be pinned, to avoid this, we tell the compiler
        // to not call the drop, i.e. simply forget that the `pool` exists, while we also make sure to drop
        // this allocated memory pool manually when the [`BufPool`] itself is dropped
        std::mem::forget(slice);

        let mut ptrs = Vec::with_capacity(count);
        for i in 0..count {
            let p = unsafe { base_ptr.add(i * pool.cfg.chunk_size) };
            ptrs.push(BPPtr { ptr: p });
        }

        Self {
            count: count,
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
                        state.free(ptr, pool);
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
                let base = slots[0].ptr;

                let _ = unsafe { Vec::from_raw_parts(base, total, total) };
            }
        }
    }
}

#[derive(Debug)]
enum AllocSlotType {
    Pool(Vec<BPPtr>),
    Dynamic(Vec<BPPtr>),
}

impl AllocSlotType {
    fn slots(&mut self) -> &mut Vec<BPPtr> {
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
