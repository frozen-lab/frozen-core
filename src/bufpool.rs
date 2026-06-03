//! A low-latency memory-budgeted buffer pool to manage fixed-sized buffer allocations
//!
//! ## Memory Allocations
//!
//! All the allocations are allocated using the global memory allocator as requested (on-the-fly).
//!
//! While a single allocation retunred as [`BufPoolAllocation`] is a large contineous slice of
//! memory w/ size as `BufPoolCfg::buffer_size.bytes() * n_buffers`.
//!
//! Memory layout structure,
//!
//! ```text
//! allocation = [[buf0][buf1][buf2]]
//! where,
//!   - every buffer is of size `buffer_size`
//!   - each buffer is pointed using `*mut u8`
//! ```
//!
//! ## Backpressure
//!
//! Every allocation reserves a memory budget and is only allowed to allocate memory if enough
//! budget (i.e. memory space) is available. Otherwise, the caller is blocked/polled till enough
//! space is available.
//!
//! When the [`BufPoolAllocation`] and all its references are dropped, the underlying memory is
//! deallocated while relaxing the budget and dropping the backpressure (if any).
//!
//! _NOTE:_ There is no faireness guarantee for the caller's who are polled when faced with
//! backpressure, as the waiting callers are awaken opportunistically.
//!
//! ## Benchmarks
//!
//! Observed measurements of latency and throughput,
//!
//! ```md
//! | Metric                       | Value              |
//! |:-----------------------------|:-------------------|
//! | Allocation Latency (avg)     | ~254 nanosecond    |
//! | Allocation Throughput (avg)  | ~3.94 million/sec  |
//! ```
//!
//! _NOTE:_ All measurements includes the complete RAII lifecycle (i.e. allocation + deallocation).
//!
//! Observed allocation latency for `N` buffers,
//!
//! ```md
//! | Buffers  | Latency  |
//! |:---------|:---------|
//! | 0x01     | 246 ns   |
//! | 0x10     | 251 ns   |
//! | 0x400    | 300 ns   |
//! ```
//!
//! _INFO:_ As seen, the allocation latency stays near constant irrespective to the size of buffers
//! and the allocated bytes.
//!
//! Environment used for benching,
//!
//! * OS: NixOS (WSL2)
//! * Architecture: x86_64
//! * Memory: 8 GiB RAM (DDR4)
//! * Rust: rustc 1.86.0 w/ cargo 1.86.0
//! * Kernel: Linux 6.6.87.2-microsoft-standard-WSL2
//! * CPU: Intel® Core™ i5-10300H @ 2.50GHz (4C / 8T)
//!
//! ## Example
//!
//! ```
//! use frozen_core::{
//!     bufpool::{BufPool, BufPoolCfg, BufferPointer},
//!     utils::BufferSize,
//! };
//!
//! const BUF_SIZE: BufferSize = BufferSize::S16;
//!
//! let pool = BufPool::new(BufPoolCfg {
//!     buffer_size: BUF_SIZE,
//!     max_memory: BUF_SIZE as usize * 0x40,
//! });
//!
//! let alloc = pool.allocate(0x2A);
//!
//! assert_eq!(alloc.length(), 0x2A);
//! assert!(!alloc.first().is_null());
//! assert_eq!(alloc.allocated_bytes(), BUF_SIZE as usize * 0x2A);
//!
//! let ptrs: Vec<BufferPointer> = alloc.iter().collect();
//! assert_eq!(ptrs.len(), 0x2A);
//! ```

use std::{alloc, ptr, sync, sync::atomic};

/// An unsafe pointer to an individual in memory buffer
///
/// ## Safety
///
/// The pointer is untyped and uninitialized. Caller is responsible for:
///
/// * Writes stay within the bounds, while the size of each buffer is [`BufPoolCfg::buffer_size`]
/// * Reads should only occur after initilization/write is completed on the buffer
/// * The pointer must not outlive the lifetime of [`BufPoolAllocation`] object
///
/// ## Example
///
/// ```
/// use frozen_core::{
///     bufpool::{BufPool, BufPoolCfg},
///     utils::BufferSize,
/// };
///
/// const BUF_SIZE: BufferSize = BufferSize::S16;
/// const BUFFER: [u8; BUF_SIZE as usize] = [1u8; BUF_SIZE as usize];
///
/// let pool = BufPool::new(BufPoolCfg {
///     buffer_size: BUF_SIZE,
///     max_memory: BUF_SIZE as usize * 0x0A,
/// });
///
/// let alloc = pool.allocate(1);
/// unsafe {
///     std::ptr::copy_nonoverlapping(BUFFER.as_ptr(), alloc.first(), BUF_SIZE as usize);
/// }
/// ```
pub type BufferPointer = *mut u8;

/// All the available configrations for [`BufPool`]
///
/// ## Example
///
/// ```
/// use frozen_core::{bufpool::BufPoolCfg, utils::BufferSize};
///
/// const BUF_SIZE: BufferSize = BufferSize::S64;
///
/// let cfg = BufPoolCfg {
///     buffer_size: BUF_SIZE,
///     max_memory: BUF_SIZE as usize * 0x1000,
/// };
///
/// assert_ne!(cfg.max_memory, 0);
/// assert!(cfg.max_memory > cfg.buffer_size.bytes());
/// ```
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BufPoolCfg {
    /// Size (in bytes) of an indivdual buffer unit allocated
    pub buffer_size: crate::utils::BufferSize,

    /// Maximum allowed memory (in bytes) to be simultaneosuly allocated by [`BufPool`]
    ///
    /// _IMPORTANT:_ When trying to allocate more memory then [`BufPoolCfg::max_memory`] via
    /// [`BufPool::allocate`], a deadlock will happen due to memory budgeting in place. The caller
    /// must make sure the `max_meory` is high enough to avoid this scenerio.
    ///
    /// _NOTE:_ To avoid backpressure, set the `max_memory` to an arbitrary large value. This
    /// would not have any direct impact on performance or resource usage, and will avoid
    /// backpressure under heavy workload.
    pub max_memory: usize,
}

/// An implementation of a low-latency memory-budgeted buffer pool managing fixed-sized buffer
/// allocations
///
/// ## Blocking `drop`
///
/// Dropping the [`BufPool`] instance from memory blocks unitl all the allocated instances of
/// [`BufPoolAllocations`] and all there references are dropped from memory.
///
/// This is in place to avoid memory leaks, as well as to enable sending [`BufPoolAllocation`]
/// objects across threads while being tied to the lifecyle of [`BufPool`].
///
/// ## Memory Allocations
///
/// All the allocations are allocated using the global memory allocator as requested (on-the-fly).
///
/// While a single allocation retunred as [`BufPoolAllocation`] is a large contineous slice of
/// memory w/ size as `BufPoolCfg::buffer_size.bytes() * n_buffers`.
///
/// Memory layout structure,
///
/// ```text
/// allocation = [[buf0][buf1][buf2]]
/// where,
///   - every buffer is of size `buffer_size`
///   - each buffer is pointed using `*mut u8`
/// ```
///
/// ## Backpressure
///
/// Every allocation reserves a memory budget and is only allowed to allocate memory if enough
/// budget (i.e. memory space) is available. Otherwise, the caller is blocked/polled till enough
/// space is available.
///
/// When the [`BufPoolAllocation`] and all its references are dropped, the underlying memory is
/// deallocated while relaxing the budget and dropping the backpressure (if any).
///
/// _NOTE:_ There is no faireness guarantee for the caller's who are polled when faced with
/// backpressure, as the waiting callers are awaken opportunistically.
///
/// ## Example
///
/// ```
/// use frozen_core::{
///     bufpool::{BufPool, BufPoolCfg, BufferPointer},
///     utils::BufferSize,
/// };
///
/// const BUF_SIZE: BufferSize = BufferSize::S16;
///
/// let pool = BufPool::new(BufPoolCfg {
///     buffer_size: BUF_SIZE,
///     max_memory: BUF_SIZE as usize * 0x40,
/// });
///
/// let alloc = pool.allocate(0x30);
///
/// assert_eq!(alloc.length(), 0x30);
/// assert!(!alloc.first().is_null());
/// assert_eq!(alloc.allocated_bytes(), BUF_SIZE as usize * 0x30);
///
/// let ptrs: Vec<BufferPointer> = alloc.iter().collect();
/// assert_eq!(ptrs.len(), 0x30);
/// ```
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

unsafe impl Send for BufPool {}
unsafe impl Sync for BufPool {}

impl BufPool {
    /// Create a new instance of [`BufPool`]
    ///
    /// ## Debug Assertions
    ///
    /// In debug builds, this function uses `debug_assertion` to prevent invalid configurations.
    /// Caller must refer to [`BufPoolCfg`] for details about the config params.
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{
    ///     bufpool::{BufPool, BufPoolCfg},
    ///     utils::BufferSize,
    /// };
    ///
    /// const BUF_SIZE: BufferSize = BufferSize::S16;
    ///
    /// let pool = BufPool::new(BufPoolCfg {
    ///     buffer_size: BUF_SIZE,
    ///     max_memory: BUF_SIZE as usize * 0x0A,
    /// });
    ///
    /// let alloc = pool.allocate(1);
    ///
    /// assert_eq!(alloc.length(), 1);
    /// assert_eq!(alloc.allocated_bytes(), BUF_SIZE as usize);
    /// ```
    #[inline]
    pub fn new(cfg: BufPoolCfg) -> Self {
        // sanity check
        debug_assert!(
            cfg.buffer_size.bytes() < cfg.max_memory,
            "MAX_MEMORY must always be larger than the BUFFER_SIZE"
        );

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

    /// Allocate `required` number of buffers each of [`BufPoolCfg::buffer_size`] size
    ///
    /// ## Allocation Layout
    ///
    /// The allocation is a large contineous slice of memory w/ size as
    ///
    /// ```text
    /// BufPoolCfg::buffer_size.bytes() * n_buffers
    /// ```
    ///
    /// Memory layout structure,
    ///
    /// ```text
    /// allocation = [[buf0][buf1][buf2]]
    /// where,
    ///   - every buffer is of size `buffer_size`
    ///   - each buffer is pointed using `*mut u8`
    /// ```
    ///
    /// ## RAII Safety
    ///
    /// The allocation object, i.e. [`BufPoolAllocation`], is RAII safe. The allocated memory is
    /// automatically deallocated as soon as the last reference to the object is dropped, while also
    /// relaxing the memory budget to eliminate backpressure (if any).
    ///
    /// ## Important Considerations
    ///
    /// The number of buffers required should never exceed `u16::MAX`. This is an abstract soft
    /// limit and should be enforced by the public interface to avoid any weird exhaustion issues
    /// or unknown bugs across the storage system.
    ///
    /// As `u16::MAX` is large enough value to almost never cause any problems for a single write
    /// operation, this soft limit acts as a guidline to safely operate with arithmatic operations
    /// across storage engine(s), including but not limited to [`frozen_core`].
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{
    ///     bufpool::{BufPool, BufPoolCfg, BufferPointer},
    ///     utils::BufferSize,
    /// };
    ///
    /// const BUF_SIZE: BufferSize = BufferSize::S16;
    ///
    /// let pool = BufPool::new(BufPoolCfg {
    ///     buffer_size: BUF_SIZE,
    ///     max_memory: BUF_SIZE as usize * 0x14,
    /// });
    ///
    /// let alloc = pool.allocate(0x0A);
    ///
    /// assert_eq!(alloc.length(), 0x0A);
    /// assert!(!alloc.first().is_null());
    /// assert_eq!(alloc.allocated_bytes(), BUF_SIZE as usize * 0x0A);
    ///
    /// let ptrs: Vec<BufferPointer> = alloc.iter().collect();
    /// assert_eq!(ptrs.len(), 0x0A);
    /// ```
    #[inline(always)]
    pub fn allocate(&self, required: usize) -> BufPoolAllocation {
        // sanity checks
        debug_assert!(required > 0, "required buffers must never be 0");
        debug_assert!(
            required * self.cfg.buffer_size.bytes() <= self.cfg.max_memory,
            "Total required bytes must be smaller then the MAX_MEMORY allowed to avoid deadlock"
        );
        debug_assert!(
            required * self.cfg.buffer_size.bytes() <= self.cfg.max_memory,
            "Total required bytes must never exceed `u16::MAX` to avoid arithmatic overflows"
        );

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
    /// ## Why we ignore [`std::sync::PoisonError`]
    ///
    /// The mutex used for lock, is solely used as a parking primitive for [`Condvar`] and does not
    /// protect any mutable state. All the pool invariants and accounting are maintained via
    /// atomics and are completely seperated from the mutex.
    ///
    /// A poisoned mutex only indicates that another tx panicked while holding the lock, and
    /// indicates an inconsistent state of the protected value. Since no state can be left
    /// partially modified under this lock, there is no possible consistency risk to recover from
    /// and propagating the poison error would only introduce unnecessary failures into the
    /// allocation path.
    ///
    /// Therefore, as best effort, we consume the [`std::sync::PoisonError`] and continue operating
    /// with the recovered guard.
    #[inline]
    fn backpressure(&self, required_bytes: usize) {
        let mut guard = self.allocation_lock.lock().unwrap_or_else(|e| e.into_inner());
        while self.allocated_memory.load(atomic::Ordering::Acquire) + required_bytes > self.cfg.max_memory {
            guard = self.allocation_cv.wait(guard).unwrap_or_else(|e| e.into_inner());
        }
    }
}

impl Drop for BufPool {
    fn drop(&mut self) {
        // NOTE: See [`BufPool::backpressure`] implementation for rationale behind poison recovery

        let mut guard = self.shutdown_lock.lock().unwrap_or_else(|e| e.into_inner());
        while self.active_allocations.load(atomic::Ordering::Acquire) != 0 {
            guard = self.shutdown_cv.wait(guard).unwrap_or_else(|e| e.into_inner());
        }
    }
}

/// A RAII safe allocation object containing allocated buffers
///
/// ## Lifetime
///
/// The object can/may outlive the scope that created it, while also being able to transfer across
/// threads. As, internally the [`BufPool`] tracks all the active allocations and delays the drop
/// until every allocation and all there references are dropped from memory.
///
/// ## Example
///
/// ```
/// use frozen_core::{
///     bufpool::{BufPool, BufPoolCfg, BufferPointer},
///     utils::BufferSize,
/// };
///
/// const BUF_SIZE: BufferSize = BufferSize::S16;
///
/// let pool = BufPool::new(BufPoolCfg {
///     buffer_size: BUF_SIZE,
///     max_memory: BUF_SIZE as usize * 0x10,
/// });
///
/// let alloc = pool.allocate(0x0A);
///
/// assert_eq!(alloc.length(), 0x0A);
/// assert!(!alloc.first().is_null());
/// assert_eq!(alloc.allocated_bytes(), BUF_SIZE as usize * 0x0A);
///
/// let ptrs: Vec<BufferPointer> = alloc.iter().collect();
/// assert_eq!(ptrs.len(), 0x0A);
/// ```
#[derive(Debug)]
pub struct BufPoolAllocation {
    buffers: usize,
    layout: alloc::Layout,
    pointer: ptr::NonNull<u8>,
    pool: ptr::NonNull<BufPool>,
    required_bytes: usize,
}

unsafe impl Send for BufPoolAllocation {}

impl BufPoolAllocation {
    /// Returns a [`BufferPointer`] to the first buffer from the allocated list of buffers
    ///
    /// _NOTE:_ The returned [`BufferPointer`] can also be used as a _base_pointer_ to operate on
    /// the entire allocated memory slice.
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{
    ///     bufpool::{BufPool, BufPoolCfg},
    ///     utils::BufferSize,
    /// };
    ///
    /// const BUF_SIZE: BufferSize = BufferSize::S32;
    ///
    /// let pool = BufPool::new(BufPoolCfg {
    ///     buffer_size: BUF_SIZE,
    ///     max_memory: BUF_SIZE as usize * 0x0A,
    /// });
    ///
    /// let alloc = pool.allocate(0x0A);
    /// assert!(!alloc.first().is_null());
    /// ```
    #[inline]
    pub const fn first(&self) -> BufferPointer {
        self.pointer.as_ptr()
    }

    /// Returns the total number of allocated buffers
    ///
    /// _IMPORTANT:_ The returned value is always equal to the `required` value using while
    /// calling [`BufPool::allocate`].
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{
    ///     bufpool::{BufPool, BufPoolCfg},
    ///     utils::BufferSize,
    /// };
    ///
    /// const BUF_SIZE: BufferSize = BufferSize::S64;
    ///
    /// let pool = BufPool::new(BufPoolCfg {
    ///     buffer_size: BUF_SIZE,
    ///     max_memory: BUF_SIZE as usize * 0x0A,
    /// });
    ///
    /// let alloc = pool.allocate(0x0A);
    /// assert_eq!(alloc.length(), 0x0A);
    /// ```
    #[inline]
    pub const fn length(&self) -> usize {
        self.buffers
    }

    /// Returns the total number of bytes of memory allocated
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{
    ///     bufpool::{BufPool, BufPoolCfg},
    ///     utils::BufferSize,
    /// };
    ///
    /// const BUF_SIZE: BufferSize = BufferSize::S16;
    ///
    /// let pool = BufPool::new(BufPoolCfg {
    ///     buffer_size: BUF_SIZE,
    ///     max_memory: BUF_SIZE as usize * 0x0A,
    /// });
    ///
    /// let alloc = pool.allocate(0x0A);
    /// assert_eq!(alloc.allocated_bytes(), BUF_SIZE as usize * 0x0A);
    /// ```
    #[inline]
    pub const fn allocated_bytes(&self) -> usize {
        self.required_bytes
    }

    /// A custom [`Iterator`] implementation to enable iteration over the list of allocated buffers
    /// from [`BufPoolAllocation`]
    ///
    /// _NOTE:_ Each yielded pointer refers to a unique individual buffer each of size
    /// [`BufPoolCfg::buffer_size`].
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::{
    ///     bufpool::{BufPool, BufPoolCfg, BufferPointer},
    ///     utils::BufferSize,
    /// };
    ///
    /// const BUF_SIZE: BufferSize = BufferSize::S16;
    ///
    /// let pool = BufPool::new(BufPoolCfg {
    ///     buffer_size: BUF_SIZE,
    ///     max_memory: BUF_SIZE as usize * 0x14,
    /// });
    ///
    /// let alloc = pool.allocate(0x0A);
    /// let ptrs: Vec<BufferPointer> = alloc.iter().collect();
    ///
    /// assert_eq!(ptrs.len(), 0x0A);
    /// ```
    #[inline]
    pub fn iter(&self) -> BufPoolAllocationIter {
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

/// A custom [`Iterator`] object to iterate over the list of allocated buffers
///
/// _NOTE:_ Buffers are yielded in allocation order and are backed by a single contiguous memory
/// region.
///
/// ## Example
///
/// ```rs
/// use frozen_core::{
///     bufpool::{BufPool, BufPoolCfg, BufferPointer},
///     utils::BufferSize,
/// };
///
/// const BUF_SIZE: BufferSize = BufferSize::S32;
///
/// let pool = BufPool::new(BufPoolCfg {
///     buffer_size: BUF_SIZE,
///     max_memory: BUF_SIZE as usize * 0x14,
/// });
///
/// let alloc = pool.allocate(0x0A);
/// let ptrs: Vec<BufferPointer> = alloc.iter().collect();
///
/// assert_eq!(ptrs.len(), 0x0A);
/// ```
#[derive(Debug)]
pub struct BufPoolAllocationIter {
    pointer: ptr::NonNull<u8>,
    buffer_size: usize,
    remaining: usize,
}

impl Iterator for BufPoolAllocationIter {
    type Item = BufferPointer;

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
/// _NOTE:_ Use of `unwrap` is totally safe as the panic, if any, would be caught by unit tests and
/// would be the indication of incorrect impl and not any runtime failures.
#[inline]
fn create_layout(required_bytes: usize) -> alloc::Layout {
    match alloc::Layout::array::<u8>(required_bytes) {
        Ok(layout) => layout,
        Err(e) => panic!("Invalid Layout: {e}"),
    }
}

/// Allocate a memory slice with given allocation `layout`
///
/// ## Allocation Failure
///
/// If the allocator is unable to satisfy the request (typically due to an OOM condition),
/// [`alloc::alloc`] returns a null pointer.
///
/// In such cases we delegate to [`alloc::handle_alloc_error`], matching the behavior of std library
/// types such as [`Vec`], [`Box`] and [`String`].
///
/// This path aborts the process and never returns. Allocation failures are therefore treated as
/// fatal runtime conditions rather than recoverable errors.
///
/// Under normal operation this path should never be reached, as memory usage is expected to be
/// bounded by the buffer pools memory budget and backpressure mechanisms.
///
/// ## Why not return `FrozenErr`
///
/// A null return from [`alloc::alloc`] indicates that the global allocator itself was unable to
/// satisfy the request.
///
/// Delegating to [`alloc::handle_alloc_error`] matches the behavior of standard library containers
/// and avoids continuing execution after a catastrophic allocator failure, where further
/// allocations required for error handling, logging or recovery may also fail.
#[inline]
fn allocate_layout(layout: alloc::Layout) -> ptr::NonNull<u8> {
    let pointer = unsafe { alloc::alloc(layout) };
    match ptr::NonNull::new(pointer) {
        Some(p) => p,
        None => alloc::handle_alloc_error(layout),
    }
}

/// Deallocate the manually allocated slice of memory with help of given `pointer` and mem `layout`
#[inline]
fn deallocate_memory(pointer: ptr::NonNull<u8>, layout: alloc::Layout) {
    unsafe { alloc::dealloc(pointer.as_ptr(), layout) };
}

#[cfg(test)]
mod tests {
    use super::*;

    const BUF_SIZE: crate::utils::BufferSize = crate::utils::BufferSize::S32;

    #[inline]
    fn create_bufpool(max_mem: usize) -> BufPool {
        BufPool::new(BufPoolCfg {
            buffer_size: BUF_SIZE,
            max_memory: max_mem,
        })
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn err_new_with_invalid_cfg() {
        create_bufpool(BUF_SIZE.bytes() >> 1);
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn err_alloc_zero() {
        let bpool = create_bufpool(BUF_SIZE.bytes());
        let _ = bpool.allocate(0);
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn err_alloc_more_then_max_memory() {
        let bpool = create_bufpool(BUF_SIZE.bytes());
        let _ = bpool.allocate(2);
    }

    #[test]
    fn ok_alloc_single() {
        let bpool = create_bufpool(BUF_SIZE.bytes() * 2);
        let alloc = bpool.allocate(1);

        assert_eq!(alloc.buffers, 1);
        assert_eq!(alloc.required_bytes, BUF_SIZE.bytes());
    }

    #[test]
    fn ok_alloc_multiple() {
        let bpool = create_bufpool(BUF_SIZE.bytes() * 0x14);
        let alloc = bpool.allocate(0x10);

        assert_eq!(alloc.buffers, 0x10);
        assert_eq!(alloc.required_bytes, BUF_SIZE.bytes() * 0x10);
    }

    #[test]
    fn ok_alloc_max_memory() {
        let bpool = create_bufpool(BUF_SIZE.bytes() * 0x0A);
        let alloc = bpool.allocate(0x0A);

        assert_eq!(alloc.buffers, 0x0A);
        assert_eq!(alloc.required_bytes, BUF_SIZE.bytes() * 0x0A);
    }

    #[test]
    fn ok_alloc_updates_memory_accounting() {
        let bpool = create_bufpool(BUF_SIZE.bytes() * 0x14);
        let alloc = bpool.allocate(0x10);

        assert_eq!(
            bpool.allocated_memory.load(atomic::Ordering::Acquire),
            BUF_SIZE.bytes() * 0x10
        );
        drop(alloc);
        assert_eq!(bpool.allocated_memory.load(atomic::Ordering::Acquire), 0);
    }

    #[test]
    fn ok_alloc_updates_active_allocation_tracking() {
        let bpool = create_bufpool(BUF_SIZE.bytes() * 0x2A);

        let alloc1 = bpool.allocate(0x10);
        let alloc2 = bpool.allocate(0x10);

        assert_eq!(bpool.active_allocations.load(atomic::Ordering::Acquire), 2);
        let _ = (drop(alloc1), drop(alloc2));
        assert_eq!(bpool.active_allocations.load(atomic::Ordering::Acquire), 0);
    }

    #[test]
    fn ok_alloc_decrments_allocated_memory_after_deallocations() {
        let bpool = create_bufpool(BUF_SIZE.bytes() * 0x80);
        let allocations: Vec<_> = (0..0x20).map(|_| bpool.allocate(2)).collect();

        assert_eq!(bpool.allocated_memory.load(atomic::Ordering::Acquire), 0x20 * 0x40);
        drop(allocations);
        assert_eq!(bpool.allocated_memory.load(atomic::Ordering::Acquire), 0);
    }

    #[test]
    fn ok_backpressure_blocks_till_memory_is_deallocated() {
        let bpool = sync::Arc::new(create_bufpool(BUF_SIZE.bytes() * 2));
        let alloc = bpool.allocate(1);

        let pool2 = bpool.clone();
        let barrier = sync::Arc::new(sync::Barrier::new(2));
        let barrier2 = barrier.clone();

        let handle = std::thread::spawn(move || {
            barrier2.wait();

            let start = std::time::Instant::now();
            let _alloc = pool2.allocate(2);

            start.elapsed()
        });

        barrier.wait();

        std::thread::sleep(std::time::Duration::from_millis(100));
        drop(alloc);

        let elapsed = handle.join().expect("allocation thread should not panic");
        assert!(elapsed >= std::time::Duration::from_millis(100));
    }

    #[test]
    fn ok_concurrent_allocations() {
        let pool = sync::Arc::new(create_bufpool(BUF_SIZE.bytes() * 0x1000));

        let mut handles = Vec::new();
        for _ in 0..0x0A {
            let pool = pool.clone();

            handles.push(std::thread::spawn(move || {
                for _ in 0..0x64 {
                    drop(pool.allocate(1));
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(pool.allocated_memory.load(atomic::Ordering::Acquire), 0);
        assert_eq!(pool.active_allocations.load(atomic::Ordering::Acquire), 0);
    }

    mod drop {
        use super::*;

        #[test]
        fn ok_partial_drop_updates_accounting() {
            let bpool = create_bufpool(BUF_SIZE.bytes() * 0x0A);

            let alloc1 = bpool.allocate(2);
            let alloc2 = bpool.allocate(2);

            assert_eq!(
                bpool.allocated_memory.load(atomic::Ordering::Acquire),
                BUF_SIZE.bytes() * 4
            );
            drop(alloc1);

            assert_eq!(
                bpool.allocated_memory.load(atomic::Ordering::Acquire),
                BUF_SIZE.bytes() * 2
            );
            drop(alloc2);

            assert_eq!(bpool.allocated_memory.load(atomic::Ordering::Acquire), 0);
        }

        #[test]
        fn ok_drop_waits_for_active_allocations() {
            let bpool = sync::Arc::new(create_bufpool(BUF_SIZE.bytes() * 0x1A));
            let alloc = bpool.allocate(0x10);

            let handle = std::thread::spawn(move || {
                drop(bpool);
            });

            std::thread::sleep(std::time::Duration::from_millis(0x64));
            assert!(!handle.is_finished());
            drop(alloc);

            handle.join().unwrap();
        }
    }

    mod memory_tests {
        use super::*;

        #[test]
        fn ok_create_layout() {
            let layout = create_layout(0x1000);

            assert_eq!(layout.align(), 1);
            assert_eq!(layout.size(), 0x1000);
        }

        #[test]
        #[should_panic(expected = "Invalid Layout")]
        fn err_create_layout() {
            create_layout(usize::MAX);
        }

        #[test]
        fn ok_allocate_layout() {
            let layout = create_layout(0x10);
            let pointer = allocate_layout(layout);
            let raw_ptr = pointer.as_ptr();

            assert!(!raw_ptr.is_null());
            deallocate_memory(pointer, layout);
        }

        #[test]
        fn ok_allocate_layout_allows_write() {
            let layout = create_layout(0x80);
            let pointer = allocate_layout(layout);

            unsafe {
                pointer.as_ptr().write(0x40);
                assert_eq!(pointer.as_ptr().read(), 0x40);
            }

            deallocate_memory(pointer, layout);
        }

        #[test]
        fn ok_allocate_layout_allows_write_to_entire_slice() {
            let layout = create_layout(0x200);
            let pointer = allocate_layout(layout);

            unsafe {
                for i in 0..0x200 {
                    pointer.as_ptr().add(i).write((i % 0xFF) as u8);
                }

                for i in 0..0x200 {
                    assert_eq!(pointer.as_ptr().add(i).read(), (i % 0xFF) as u8);
                }
            }

            deallocate_memory(pointer, layout);
        }
    }

    mod alloc_struct {
        use super::*;

        #[test]
        fn ok_first_returns_ptr_to_first_buf_from_alloc() {
            let bpool = create_bufpool(BUF_SIZE.bytes() * 0x20);
            let alloc = bpool.allocate(0x10);

            assert_eq!(alloc.first(), alloc.pointer.as_ptr());
        }

        #[test]
        fn ok_length_returns_length_of_alloc() {
            let bpool = create_bufpool(BUF_SIZE.bytes() * 0x20);
            let alloc = bpool.allocate(0x10);

            assert_eq!(alloc.length(), alloc.buffers);
        }

        #[test]
        fn ok_allocated_bytes_return_total_allocated_bytes() {
            let bpool = create_bufpool(BUF_SIZE.bytes() * 0x20);
            let alloc = bpool.allocate(0x10);

            assert_eq!(alloc.allocated_bytes(), alloc.buffers * BUF_SIZE.bytes());
        }

        #[test]
        fn ok_alloc_can_be_shared_across_threads() {
            let pool = sync::Arc::new(create_bufpool(BUF_SIZE.bytes() * 2));
            let alloc = pool.allocate(1);

            std::thread::spawn(move || {
                drop(alloc);
            })
            .join()
            .unwrap();
        }
    }

    mod iterator {
        use super::*;

        #[test]
        fn ok_iter_yeilds_all_buffers() {
            let bpool = create_bufpool(BUF_SIZE.bytes() * 0x0A);
            let alloc = bpool.allocate(4);

            let ptrs: Vec<_> = alloc.iter().collect();
            assert_eq!(ptrs.len(), 4);

            assert_eq!(ptrs[1] as usize - ptrs[0] as usize, 0x20);
            assert_eq!(ptrs[2] as usize - ptrs[1] as usize, 0x20);
            assert_eq!(ptrs[3] as usize - ptrs[2] as usize, 0x20);
        }

        #[test]
        fn ok_iter_yeilds_none_when_exhausted() {
            let bpool = create_bufpool(BUF_SIZE.bytes() * 0x0A);
            let alloc = bpool.allocate(2);
            let mut iter = alloc.iter();

            assert!(iter.next().is_some());
            assert!(iter.next().is_some());
            assert!(iter.next().is_none());
            assert!(iter.next().is_none());
        }
    }
}
