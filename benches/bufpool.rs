//! Benchmarks for `bufpool` module
//! Run using: `taskset -c 2,3,4 cargo bench --bench bufpool --features=bufpool`

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use frozen_core::{
    bufpool::{BufPool, BufPoolCfg},
    utils::BufferSize,
};
use std::{hint::black_box, sync::Arc};

const MID: u8 = 0;
const BUF_SIZE: BufferSize = BufferSize::S64;

#[inline]
fn new_pool(max_memory: usize) -> BufPool {
    BufPool::new(BufPoolCfg { module_id: MID, buffer_size: BUF_SIZE, max_memory })
}

fn bench_bpool(c: &mut Criterion) {
    let mut group = c.benchmark_group("bpool");

    //
    // allocation latency
    //

    for &n in &[1, 0x10, 0x400] {
        group.bench_with_input(BenchmarkId::new("alloc_latency", n), &n, |b, &n| {
            let pool = new_pool(usize::MAX >> 2);

            b.iter(|| {
                let alloc = pool.allocate(black_box(n));
                black_box(alloc);
            });
        });
    }

    //
    // contention across threads
    //

    for &threads in &[1, 2, 4] {
        group.bench_with_input(BenchmarkId::new("alloc_contention", threads), &threads, |b, &threads| {
            let pool = Arc::new(new_pool(usize::MAX >> 2));

            b.iter(|| {
                std::thread::scope(|s| {
                    for _ in 0..threads {
                        let pool = pool.clone();
                        s.spawn(move || {
                            black_box(pool.allocate(8));
                        });
                    }
                });
            });
        });
    }

    //
    // throughput
    //

    group.bench_function("throughput", |b| {
        let pool = new_pool(usize::MAX >> 2);

        b.iter(|| {
            for _ in 0..0x400 {
                black_box(pool.allocate(8));
            }
        });
    });

    group.finish();
}

criterion_group!(benches, bench_bpool);
criterion_main!(benches);
