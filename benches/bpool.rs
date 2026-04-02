//! Benchmarks for `bpool` module
//! Run using: `taskset -c 2 cargo bench --bench bpool --features=bpool`

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use frozen_core::bpool::{BPBackend, BPCfg, BufPool};
use std::hint::black_box;
use std::sync::Arc;

const MID: u8 = 0;

fn new_dynamic() -> BufPool {
    BufPool::new::<MID>(BPCfg {
        chunk_size: 64,
        backend: BPBackend::Dynamic,
    })
}

fn new_prealloc(cap: usize) -> BufPool {
    BufPool::new::<MID>(BPCfg {
        chunk_size: 64,
        backend: BPBackend::Prealloc { capacity: cap },
    })
}

fn bench_bpool(c: &mut Criterion) {
    let mut group = c.benchmark_group("bpool");

    // Single tx latency
    for &n in &[1, 4, 0x10, 0x40] {
        let dyn_pool = new_dynamic();
        let pre_pool = new_prealloc(0x400);

        // w/ dynamic backend
        group.bench_with_input(BenchmarkId::new("single_dyn", n), &n, |b, &n| {
            b.iter(|| {
                let alloc = dyn_pool.allocate(black_box(n)).unwrap();
                black_box(alloc);
            });
        });

        // w/ pre-allocated backend
        group.bench_with_input(BenchmarkId::new("single_pre", n), &n, |b, &n| {
            b.iter(|| {
                let alloc = pre_pool.allocate(black_box(n)).unwrap();
                black_box(alloc);
            });
        });
    }

    // benching scaling cost (batch size)
    let pre_pool = new_prealloc(0x1000);
    for &n in &[1, 8, 0x20, 0x80] {
        group.bench_with_input(BenchmarkId::new("scaling_pre", n), &n, |b, &n| {
            b.iter(|| {
                let alloc = pre_pool.allocate(black_box(n)).unwrap();
                black_box(alloc);
            });
        });
    }

    // benching contention (multi tx)
    for &threads in &[2, 4, 8] {
        group.bench_with_input(BenchmarkId::new("contention_pre", threads), &threads, |b, &threads| {
            let pool = Arc::new(new_prealloc(1024));

            b.iter(|| {
                std::thread::scope(|s| {
                    for _ in 0..threads {
                        let pool = pool.clone();
                        s.spawn(move || {
                            let alloc = pool.allocate(8).unwrap();
                            black_box(alloc);
                        });
                    }
                });
            });
        });
    }

    // benching blocking cost
    group.bench_function("blocking_prealloc", |b| {
        let pool = Arc::new(new_prealloc(8));

        b.iter(|| {
            let pool2 = pool.clone();

            let h = std::thread::spawn(move || {
                let _a = pool2.allocate(8).unwrap();
            });

            let alloc = pool.allocate(8).unwrap();
            drop(alloc);

            h.join().unwrap();
        });
    });

    // benching fallback cost when `n > cap` (from prealloc to dynamic)
    let pool = new_prealloc(0x10);
    for &n in &[0x20, 0x40, 0x80] {
        group.bench_with_input(BenchmarkId::new("fallback_dyn", n), &n, |b, &n| {
            b.iter(|| {
                let alloc = pool.allocate(black_box(n)).unwrap();
                black_box(alloc);
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_bpool);
criterion_main!(benches);
