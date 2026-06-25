#![allow(missing_docs)]

use std::{sync, sync::atomic};

const MAX_NODE: u32 = u32::MAX;

#[derive(Debug)]
pub struct Reservoir<T: Send + Sync + Sized> {
    cv: sync::Condvar,
    waiters: atomic::AtomicU32,
    nexts: Box<[atomic::AtomicU32]>,
    resources: Box<[T]>,
    lock: sync::Mutex<()>,
    head: atomic::AtomicU64,
}

impl<T> Reservoir<T>
where
    T: Send + Sync + Sized,
{
    #[inline]
    pub fn new(resources: Vec<T>) -> Self {
        let capacity = resources.len();
        assert!(capacity < MAX_NODE as usize, "Resources must not exceed u32::MAX length");

        let mut nexts = Vec::with_capacity(capacity);
        for idx in 0..(capacity as u32) {
            nexts.push(atomic::AtomicU32::new(if idx + 1 == MAX_NODE {
                MAX_NODE
            } else {
                idx + 1
            }));
        }

        Self {
            cv: sync::Condvar::new(),
            head: atomic::AtomicU64::new(0),
            lock: sync::Mutex::new(()),
            nexts: nexts.into_boxed_slice(),
            resources: resources.into_boxed_slice(),
            waiters: atomic::AtomicU32::new(0),
        }
    }

    #[inline]
    pub fn acquire(&self) -> ReservoirPermit<'_, T> {
        if let Some(index) = self.try_pop() {
            return ReservoirPermit { reservoir: self, index: index as usize };
        }

        self.waiters.fetch_add(1, atomic::Ordering::SeqCst);

        let mut guard = self.lock.lock().unwrap_or_else(|err| err.into_inner());
        loop {
            if let Some(index) = self.try_pop() {
                self.waiters.fetch_sub(1, atomic::Ordering::SeqCst);
                return ReservoirPermit { reservoir: self, index: index as usize };
            }

            guard = self.cv.wait(guard).unwrap_or_else(|e| e.into_inner());
        }
    }

    #[inline]
    fn try_pop(&self) -> Option<u32> {
        loop {
            let current_head = self.head.load(atomic::Ordering::Acquire);
            let (head, version) = unpack(current_head);

            if head == MAX_NODE {
                return None;
            }

            let next = self.nexts[head as usize].load(atomic::Ordering::Acquire);
            if self
                .head
                .compare_exchange_weak(
                    current_head,
                    pack(next, version.wrapping_add(1)),
                    atomic::Ordering::AcqRel,
                    atomic::Ordering::Acquire,
                )
                .is_ok()
            {
                return Some(head);
            }
        }
    }

    #[inline]
    fn push(&self, index: u32) {
        loop {
            let current_head = self.head.load(atomic::Ordering::Acquire);
            let (head, version) = unpack(current_head);
            self.nexts[index as usize].store(head, atomic::Ordering::Relaxed);
            if self
                .head
                .compare_exchange_weak(
                    current_head,
                    pack(index, version.wrapping_add(1)),
                    atomic::Ordering::AcqRel,
                    atomic::Ordering::Acquire,
                )
                .is_ok()
            {
                return;
            }
        }
    }

    #[inline]
    fn release(&self, index: u32) {
        self.push(index);
        if self.waiters.load(atomic::Ordering::SeqCst) > 0 {
            let _guard = self.lock.lock().unwrap_or_else(|e| e.into_inner());
            self.cv.notify_one();
        }
    }
}

#[derive(Debug)]
pub struct ReservoirPermit<'a, T: Send + Sync + Sized> {
    reservoir: &'a Reservoir<T>,
    index: usize,
}

impl<'a, T> Drop for ReservoirPermit<'a, T>
where
    T: Send + Sync + Sized,
{
    fn drop(&mut self) {
        self.reservoir.release(self.index as u32);
    }
}

impl<'a, T> std::ops::Deref for ReservoirPermit<'a, T>
where
    T: Send + Sync + Sized,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.reservoir.resources[self.index]
    }
}

impl<'a, T> std::ops::DerefMut for ReservoirPermit<'a, T>
where
    T: Send + Sync + Sized,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: We have exclusive access via the permit so the use of unsafe is perfectly sound.
        unsafe { &mut *(self.reservoir.resources.as_ptr().add(self.index) as *mut T) }
    }
}

#[inline]
fn pack(index: u32, version: u32) -> u64 {
    (version as u64) << 0x20 | index as u64
}

#[inline]
fn unpack(value: u64) -> (u32, u32) {
    (value as u32, (value >> 0x20) as u32)
}
