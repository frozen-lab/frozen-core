#![allow(missing_docs)]

use crate::utils::BufferSize;
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

    /// ## Constraints
    ///
    /// The number of buffers required should never exceed `u16::MAX`. This is an abstract soft limit and should be
    /// enforced via public interface to avoid any weird exhaustion issues or bugs across the storage system.
    ///
    /// As `u16::MAX` is large enough value to almost never cause any problems for a single write operation, this soft
    /// limit acts as a guidline to safely operate arithmatic operations across storage engine's, including but not
    /// limited to [`frozen_core`].
    #[inline(always)]
    pub fn allocate(&self, required: usize) -> BufPoolAllocation {
        let required_bytes = self.cfg.buffer_size.bytes() * required;
        loop {
            let current_bytes = self.allocated_memory.load(atomic::Ordering::Acquire);
            if current_bytes + required_bytes > self.cfg.max_memory {
                self.backpressure(required_bytes);
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

        BufPoolAllocation {
            layout,
            pointer,
            required_bytes,
            buffers: required,
            pool: ptr::NonNull::from(self),
        }
    }

    /// Applies backpressure until enough memory budget is available for the allocation
    ///
    /// ## Why we ignore [`std::sync::PoisonError`]?
    ///
    /// The mutex used for lock, is solely used as a parking primitive for [`Condvar`] and does not protect any mutable
    /// state. All the pool invariants and accounting are maintained via atomics and are completely seperated from
    /// the mutex.
    ///
    /// A poisoned mutex only indicates that another tx panicked while holding the lock, and indicates an inconsistent
    /// state of the protected value. Since no state can be left partially modified under this lock, there is no
    /// possible consistency risk to recover from and propagating the poison error would only introduce unnecessary
    /// failures into the allocation path.
    ///
    /// Therefore, as best effort, we consume the [`std::sync::PoisonError`] and continue operating with the recovered
    /// guard.
    #[inline]
    fn backpressure(&self, required_bytes: usize) {
        let mut guard = self.allocation_lock.lock().unwrap_or_else(|e| e.into_inner());
        while self.allocated_memory.load(atomic::Ordering::Acquire) + required_bytes > self.cfg.max_memory {
            guard = self.allocation_cv.wait(guard).unwrap_or_else(|e| e.into_inner());
        }
    }
}

impl Drop for BufPool {
    /// *NOTE:* See [`BufPool::backpressure`] for rationale behind poison recovery
    fn drop(&mut self) {
        let mut guard = self.shutdown_lock.lock().unwrap_or_else(|e| e.into_inner());
        while self.active_allocations.load(atomic::Ordering::Acquire) != 0 {
            guard = self.shutdown_cv.wait(guard).unwrap_or_else(|e| e.into_inner());
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
        let pool = unsafe { self.pool.as_ref() };
        deallocate_memory(self.pointer, self.layout);

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
    match alloc::Layout::array::<u8>(required_bytes) {
        Ok(layout) => layout,
        Err(e) => panic!("Invalid layout: {e}"),
    }
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
