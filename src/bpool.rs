use crate::error::{FrozenErr, FrozenRes};
use std::sync::{self, atomic};

const INVALID_POOL_SLOT: usize = u32::MAX as usize;

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
    pub fn new(capacity: usize, buf_size: usize, module_id: u8) -> Self {
        let pool_size = capacity * buf_size;
        let mut pool = Vec::<u8>::with_capacity(pool_size);
        let ptr = PoolPtr(pool.as_mut_ptr());

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

    /// Allocates `N` buffers for use in write IO ops.
    ///
    /// ## Polling
    ///
    /// This function may not allocate all the `N` required buffers in one call,
    /// so the caller must poll (wait and retry) for remaining `N` buffers.
    ///
    /// ## RAII Safety
    ///
    /// All [`BufPool`] aloocations are RAII safe by default, hence when the variable
    /// which stores the result of `allocate`, is dropped, the buffer's it holds are
    /// also automatically freed. The burden of _freeing after use_ does not fall on
    /// the caller.
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

            // local walk
            let cur = idx;
            let mut last = cur;
            let mut count = 1;
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
                Ok(_) => {
                    // materialize slots
                    let mut cur = idx;
                    for _ in 0..count {
                        batch.slots.push(self.ptr.add((cur * self.buf_size) as u64));
                        cur = self.next[cur as usize].load(atomic::Ordering::Relaxed);
                    }
                    batch.count = count;
                    return batch;
                }
                Err(h) => head = h,
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
        // as it was created, which then is dropped by Rust destructor's automatically!
        let _ = unsafe { Vec::from_raw_parts(self.ptr.ptr(), pool_size, pool_size) };
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

type TSlot = *mut u8;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct PoolPtr(TSlot);

unsafe impl Send for PoolPtr {}
unsafe impl Sync for PoolPtr {}

impl PoolPtr {
    #[inline]
    pub const fn ptr(&self) -> TSlot {
        self.0
    }

    #[inline]
    const fn add(&self, count: u64) -> Self {
        unsafe { Self(self.0.add(count as usize)) }
    }

    #[inline]
    const fn offset_from(&self, ptr: &Self) -> usize {
        unsafe { ptr.0.offset_from(self.0) as usize }
    }
}

#[derive(Debug)]
pub struct Allocation<'a> {
    pub count: usize,
    pub slots: Vec<PoolPtr>,
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
