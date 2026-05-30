#![allow(missing_docs)]
#![allow(unused)]

use crate::{error::FrozenRes, hints::unlikely};
use std::{alloc, ptr};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BufPoolCfg {
    /// Size (in bytes) of a single buffer unit returned via [`BufPoolAllocation`] upon successful allocation
    pub buffer_size: usize,
}

#[derive(Debug)]
pub struct BufPool {
    cfg: BufPoolCfg,
}

impl BufPool {
    #[inline(always)]
    pub fn allocate(&self, required: usize) -> FrozenRes<BufPoolAllocation> {
        let capacity = self.cfg.buffer_size * required;

        let layout = create_layout(capacity);
        let pointer = unsafe { allocate_layout(layout) };

        Ok(BufPoolAllocation {
            layout,
            pointer,
            buffers: required,
            buffer_size: self.cfg.buffer_size,
        })
    }
}

/// Creates a array layout with given `capacity`
///
/// *NOTE:* Use of `unwrap` is totally safe as the panic, if any, would be caught by unit tests and would be the
/// indication of incorrect impl and not any runtime failures
#[inline]
fn create_layout(capacity: usize) -> alloc::Layout {
    alloc::Layout::array::<u8>(capacity).unwrap()
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
#[inline]
fn allocate_layout(layout: alloc::Layout) -> ptr::NonNull<u8> {
    let ptr = unsafe { alloc::alloc(layout) };
    match ptr::NonNull::new(ptr) {
        Some(p) => p,
        None => alloc::handle_alloc_error(layout),
    }
}

#[derive(Debug)]
pub struct BufPoolAllocation {
    buffers: usize,
    buffer_size: usize,
    layout: alloc::Layout,
    pointer: ptr::NonNull<u8>,
}

impl BufPoolAllocation {
    /// *NOTE:* Even though it does not mutates the `self` here, we expect a mutable self to make this function
    /// a one-time use only.
    #[inline]
    pub fn iter_mut(&mut self) -> BufPoolAllocationIter {
        BufPoolAllocationIter {
            pointer: self.pointer,
            buffer_size: self.buffer_size,
            remaining: self.buffers,
        }
    }
}

impl Drop for BufPoolAllocation {
    fn drop(&mut self) {
        let capacity = self.buffers * self.buffer_size;
        if unlikely(capacity == 0) {
            return;
        }

        unsafe { alloc::dealloc(self.pointer.as_ptr(), self.layout) };
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

        let ptr = self.pointer;

        self.pointer = unsafe { self.pointer.add(self.buffer_size) };
        self.remaining -= 1;

        Some(ptr.as_ptr())
    }
}
