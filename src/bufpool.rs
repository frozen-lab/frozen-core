#![allow(missing_docs)]
#![allow(unused)]

use crate::{error::FrozenRes, hints::unlikely};

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

        let mut slice = Vec::<u8>::with_capacity(capacity);
        let base_ptr = slice.as_mut_ptr();

        // NOTE: We manually disable the destructor to pin the allocated buffers in the memory. As the allocated
        // buffers are used for IO, and may require till the caller decides to drop them. This also enables us
        // to manually construct the slice back into a vector and drop the allocated memory by using the default
        // destructor of `Vec` object.
        std::mem::forget(slice);

        Ok(BufPoolAllocation {
            base_ptr,
            buffers: required,
            buffer_size: self.cfg.buffer_size,
        })
    }
}

#[derive(Debug)]
pub struct BufPoolAllocation {
    buffers: usize,
    buffer_size: usize,
    base_ptr: *mut u8,
}

impl BufPoolAllocation {
    /// *NOTE:* Even though it does not mutates the `self` here, we expect a mutable self to make this function
    /// a one-time use only.
    #[inline]
    pub fn iter_mut(&mut self) -> BufPoolAllocationIter {
        BufPoolAllocationIter {
            base_ptr: self.base_ptr,
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

        // NOTE: after allocation, we manually pin the buffers in memory by disabling the default destructor of
        // the allocated vector. So, in order to free the allocated memory, we must recreate the vector from the
        // base pointer and let the default destructor do its thing ;)
        let _ = unsafe { Vec::from_raw_parts(self.base_ptr, capacity, capacity) };
    }
}

#[derive(Debug)]
pub struct BufPoolAllocationIter {
    base_ptr: *mut u8,
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

        let ptr = self.base_ptr;

        self.base_ptr = unsafe { self.base_ptr.add(self.buffer_size) };
        self.remaining -= 1;

        Some(ptr)
    }
}
