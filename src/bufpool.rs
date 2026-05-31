#![allow(missing_docs)]

use crate::{error::FrozenRes, hints::unlikely, utils::BufferSize};
use std::{alloc, ptr, sync, sync::atomic};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BufPoolCfg {
    /// Identifier used for error propagation by [`frozen_core::error::FrozenErr`]
    pub module_id: u8,

    /// Size (in bytes) of a single buffer unit returned via [`BufPoolAllocation`] upon successful allocation
    pub buffer_size: BufferSize,

    /// Maximum allowed memory (in bytes) to be allocated by [`BufPool`]
    ///
    /// After the limit is exhausted, incoming allocation request are polled using backpressure to limit the size
    /// of memory being used. The polling ends when existing allocations are dropped from memory decrementing current
    /// memory usage.
    ///
    /// Backpressure can be handy while running in resource constrained environments to help limit the amount of
    /// resources being used by the system.
    ///
    /// *NOTE:* To avoid backpressure, set the `max_memory` to an arbitrary large value. This would not have any direct
    /// impact on performance or resource usage, just that it'll try not to constrain the caller.
    pub max_memory: usize,
}

#[derive(Debug)]
pub struct BufPool {
    active_allocations: atomic::AtomicUsize,
    allocation_cv: sync::Condvar,
    allocation_lock: sync::Mutex<()>,
    allocated_memory: atomic::AtomicUsize,
    cfg: BufPoolCfg,
    shutdown_cv: sync::Condvar,
    shutdown_lock: sync::Mutex<()>,
}

impl BufPool {
    #[inline]
    pub fn new(cfg: BufPoolCfg) -> Self {
        Self {
            cfg,
            active_allocations: atomic::AtomicUsize::new(0),
            allocated_memory: atomic::AtomicUsize::new(0),
            allocation_cv: sync::Condvar::new(),
            allocation_lock: sync::Mutex::new(()),
            shutdown_cv: sync::Condvar::new(),
            shutdown_lock: sync::Mutex::new(()),
        }
    }

    #[inline(always)]
    pub fn allocate(&self, required: usize) -> FrozenRes<BufPoolAllocation> {
        let required_bytes = self.cfg.buffer_size.bytes() * required;
        loop {
            let current_bytes = self.allocated_memory.load(atomic::Ordering::Acquire);
            if current_bytes + required_bytes > self.cfg.max_memory {
                self.backpressure(required_bytes)?;
                continue;
            }

            match self.allocated_memory.compare_exchange(
                current_bytes,
                current_bytes + required_bytes,
                atomic::Ordering::AcqRel,
                atomic::Ordering::Acquire,
            ) {
                Ok(_) => break,
                Err(_) => continue,
            }
        }

        let layout = create_layout(required_bytes);
        let pointer = allocate_layout(layout);
        self.active_allocations.fetch_add(1, atomic::Ordering::Relaxed);

        Ok(BufPoolAllocation {
            layout,
            pointer,
            required_bytes,
            buffers: required,
            pool: ptr::NonNull::from(self),
        })
    }

    #[inline]
    fn backpressure(&self, required_bytes: usize) -> FrozenRes<()> {
        let mut guard = self
            .allocation_lock
            .lock()
            .map_err(|error| err::new_err(err::LPN, error, self.cfg.module_id))?;

        while self.allocated_memory.load(atomic::Ordering::Acquire) + required_bytes > self.cfg.max_memory {
            guard = self
                .allocation_cv
                .wait(guard)
                .map_err(|error| err::new_err(err::LPN, error, self.cfg.module_id))?;
        }

        Ok(())
    }
}

impl Drop for BufPool {
    fn drop(&mut self) {
        let mut guard = match self.shutdown_lock.lock() {
            Ok(g) => g,
            Err(_) => return,
        };

        while self.active_allocations.load(atomic::Ordering::Acquire) != 0 {
            guard = match self.shutdown_cv.wait(guard) {
                Ok(g) => g,
                Err(_) => break,
            };
        }
    }
}

#[derive(Debug)]
pub struct BufPoolAllocation {
    buffers: usize,
    layout: alloc::Layout,
    pointer: ptr::NonNull<u8>,
    pool: ptr::NonNull<BufPool>,
    required_bytes: usize,
}

impl BufPoolAllocation {
    /// *NOTE:* Even though it does not mutates the `self` here, we require a mutable self to make this function
    /// a one-time use only.
    #[inline]
    pub fn iter_mut(&mut self) -> BufPoolAllocationIter {
        let pool = unsafe { self.pool.as_ref() };
        BufPoolAllocationIter {
            pointer: self.pointer,
            buffer_size: pool.cfg.buffer_size.bytes(),
            remaining: self.buffers,
        }
    }
}

impl Drop for BufPoolAllocation {
    fn drop(&mut self) {
        if unlikely(self.required_bytes == 0) {
            return;
        }

        deallocate_memory(self.pointer, self.layout);
        let pool = unsafe { self.pool.as_ref() };

        pool.allocated_memory
            .fetch_sub(self.required_bytes, atomic::Ordering::Release);
        pool.allocation_cv.notify_one();

        if pool.active_allocations.fetch_sub(1, atomic::Ordering::Release) == 1 {
            pool.shutdown_cv.notify_one();
        }
    }
}

#[derive(Debug)]
pub struct BufPoolAllocationIter {
    pointer: ptr::NonNull<u8>,
    buffer_size: usize,
    remaining: usize,
}

impl Iterator for BufPoolAllocationIter {
    type Item = *mut u8;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        let curr_ptr = self.pointer;

        self.pointer = unsafe { self.pointer.add(self.buffer_size) };
        self.remaining -= 1;

        Some(curr_ptr.as_ptr())
    }
}

/// Creates a array layout with given `capacity`
///
/// *NOTE:* Use of `unwrap` is totally safe as the panic, if any, would be caught by unit tests and would be the
/// indication of incorrect impl and not any runtime failures
#[inline]
fn create_layout(required_bytes: usize) -> alloc::Layout {
    alloc::Layout::array::<u8>(required_bytes).unwrap()
}

/// Allocate a memory slice with given allocation `layout`
///
/// ## Allocation Failure
///
/// If the allocator is unable to satisfy the request (typically due to an OOM condition), [`alloc::alloc`] returns
/// a null pointer. In such cases we delegate to [`alloc::handle_alloc_error`], matching the behavior of std library
/// types such as [`Vec`], [`Box`] and [`String`].
///
/// This path aborts the process and never returns. Allocation failures are therefore treated as fatal runtime conditions
/// rather than recoverable errors.
///
/// Under normal operation this path should never be reached, as memory usage is expected to be bounded by the buffer
/// pools memory budget and backpressure mechanisms.
///
/// ## Why not return `FrozenErr`?
///
/// A null return from [`alloc::alloc`] indicates that the global allocator itself was unable to satisfy the request.
///
/// Delegating to [`alloc::handle_alloc_error`] matches the behavior of standard library containers and avoids continuing
/// execution after a catastrophic allocator failure, where further allocations required for error handling, logging
/// or recovery may also fail.
#[inline]
fn allocate_layout(layout: alloc::Layout) -> ptr::NonNull<u8> {
    let pointer = unsafe { alloc::alloc(layout) };
    match ptr::NonNull::new(pointer) {
        Some(p) => p,
        None => alloc::handle_alloc_error(layout),
    }
}

/// Deallocate the manually allocated slice of memory with help of given `pointer` and memory `layout`
#[inline]
fn deallocate_memory(pointer: ptr::NonNull<u8>, layout: alloc::Layout) {
    unsafe { alloc::dealloc(pointer.as_ptr(), layout) };
}

mod err {
    use crate::error::{ErrCode, FrozenErr};

    /// Domain Id for [`BufPool`] is **19**
    const ERRDOMAIN: u8 = 0x13;

    /// (02) lock/guard poisoned while waiting
    pub const LPN: ErrCode = ErrCode::new(0x02, "lock poisoned while waiting");

    #[inline]
    pub fn new_err<E: std::fmt::Display>(code: ErrCode, error: E, mid: u8) -> FrozenErr {
        FrozenErr::new_raw(mid, ERRDOMAIN, code, error)
    }
}
