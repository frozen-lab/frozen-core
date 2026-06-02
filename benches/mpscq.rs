//! Benchmarks for `mpscq` module
//! Run using: `taskset -c 2,3,4 cargo bench --bench mpscq --features=mpscq`

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use frozen_core::mpscq::MPSCQueue;
use std::hint::black_box;

fn bench_mpscq(c: &mut Criterion) {
    let mut group = c.benchmark_group("mpscq");

    for &n in &[1, 0x10, 0x20, 0x40] {
        group.bench_with_input(BenchmarkId::new("push_batch", n), &n, |b, &n| {
            let q = MPSCQueue::default();

            b.iter(|| {
                for i in 0usize..n {
                    q.push(black_box(i));
                }

                let _ = q.drain();
            });
        });

        group.bench_with_input(BenchmarkId::new("drain_batch", n), &n, |b, &n| {
            b.iter(|| {
                let q = MPSCQueue::default();

                for i in 0..n {
                    q.push(black_box(i));
                }

                black_box(q.drain());
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_mpscq);
criterion_main!(benches);
