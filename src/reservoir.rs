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

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn ok_create_and_basic_acquire() {
        let pool = Reservoir::new(vec![0x0A, 0x1A, 0x2A]);

        let permit = pool.acquire();
        assert_eq!(*permit, 0x0A);
    }

    mod deref {
        use super::*;

        #[test]
        fn ok_deref_and_deref_mut_coercion() {
            let pool = Reservoir::new(vec![String::from("hello")]);

            {
                let mut permit = pool.acquire();
                assert_eq!(permit.len(), 5);

                permit.push_str(" world");
            }

            let permit = pool.acquire();
            assert_eq!(*permit, "hello world");
        }
    }

    #[test]
    fn ok_exhaustion_and_sequential_reuse() {
        let pool = Reservoir::new(vec![1, 2]);

        let p1 = pool.acquire();
        let p2 = pool.acquire();
        drop(p1);

        let p3 = pool.acquire();
        assert_eq!(*p3, 1);
        assert_eq!(*p2, 2);
    }

    #[test]
    fn ok_acquire_blocks_until_notified() {
        let pool = Arc::new(Reservoir::new(vec![0x3C]));
        let permit = pool.acquire();

        let pool_clone = Arc::clone(&pool);
        let worker = thread::spawn(move || {
            let p = pool_clone.acquire();
            assert_eq!(*p, 0x3C);
        });

        thread::sleep(Duration::from_millis(0x32));
        drop(permit);

        worker.join().expect("Worker thread panicked");
    }

    #[test]
    fn ok_concurrent_stress_test() {
        const CAPACITY: usize = 0x0A;
        const THREADS: usize = 0x32;
        const ITERATIONS: usize = 0x64;

        let pool = Arc::new(Reservoir::new(vec![0; CAPACITY]));
        let mut handles = Vec::new();

        for _ in 0..THREADS {
            let pool_clone = Arc::clone(&pool);
            handles.push(thread::spawn(move || {
                for _ in 0..ITERATIONS {
                    let mut permit = pool_clone.acquire();
                    *permit += 1;

                    thread::yield_now();
                }
            }));
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let mut total_sum = 0;
        let mut _held_permits = Vec::with_capacity(CAPACITY);

        for _ in 0..CAPACITY {
            let permit = pool.acquire();
            total_sum += *permit;
            _held_permits.push(permit);
        }

        assert_eq!(total_sum, THREADS * ITERATIONS);
    }

    #[test]
    #[should_panic]
    fn err_zero_capacity_panics_on_acquire() {
        let pool: Reservoir<u32> = Reservoir::new(vec![]);
        let _permit = pool.acquire();
    }

    #[test]
    #[should_panic]
    fn err_capacity_exceeds_max_node() {
        let massive_vec: Vec<()> = vec![(); MAX_NODE as usize];
        let _pool = Reservoir::new(massive_vec);
    }

    #[test]
    fn ok_multiple_waiters_wake_sequentially() {
        let pool = Arc::new(Reservoir::new(vec![1, 2]));

        let p1 = pool.acquire();
        let p2 = pool.acquire();

        let mut handles = Vec::new();
        for _ in 0..3 {
            let pool_clone = Arc::clone(&pool);
            handles.push(thread::spawn(move || {
                let _permit = pool_clone.acquire();
                thread::sleep(Duration::from_millis(0x0A));
            }));
        }

        thread::sleep(Duration::from_millis(0x32));

        drop(p1);
        drop(p2);

        for handle in handles {
            handle.join().expect("Thread panicked or deadlocked");
        }

        assert_eq!(pool.resources.len(), 2);
    }

    #[test]
    fn ok_permit_dropped_on_thread_panic() {
        let pool = Arc::new(Reservoir::new(vec![0x63]));

        let pool_clone = Arc::clone(&pool);
        let result = thread::spawn(move || {
            let _permit = pool_clone.acquire();
            panic!("Intentional crash!");
        })
        .join();

        assert!(result.is_err());

        let (tx, rx) = std::sync::mpsc::channel();
        thread::spawn(move || {
            let permit = pool.acquire();
            tx.send(*permit).unwrap();
        });

        let recovered_value = rx
            .recv_timeout(Duration::from_millis(0x64))
            .expect("Permit leaked during panic! Resource was not returned.");

        assert_eq!(recovered_value, 0x63);
    }
}
