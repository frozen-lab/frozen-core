use frozen_core::bpool::{BPBackend, BPCfg, BufPool};
use std::sync::Arc;
use std::thread;

fn main() {
    let pool = Arc::new(BufPool::new(BPCfg {
        mid: 0,
        chunk_size: 0x20,
        backend: BPBackend::Prealloc { capacity: 0x10 },
    }));

    let mut threads = Vec::new();
    for _ in 0..4 {
        let pool = pool.clone();

        threads.push(thread::spawn(move || {
            for _ in 0..0x80 {
                let alloc = pool.allocate(4).expect("allocation failed");
                assert_eq!(alloc.count, 4);
            }
        }));
    }

    for t in threads {
        t.join().expect("thread failed");
    }
}
