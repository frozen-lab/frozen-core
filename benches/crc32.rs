//! Benchmarks for `crc32` module, run using `taskset -c 2 cargo bench --bench crc32 --features=crc32`

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use frozen_core::crc32::Crc32C;
use std::hint::black_box;

fn make_buf(len: usize, seed: u8) -> Vec<u8> {
    (0..len).map(|i| seed.wrapping_add(i as u8)).collect()
}

fn bench_crc_all(c: &mut Criterion) {
    let crc = Crc32C::default();
    let mut group = c.benchmark_group("crc32c");

    // we test w/ multiple sizes (4KiB, 64KiB & 1MiB)
    for &size in &[0x1000, 0x10000, 0x100000] {
        let b0 = make_buf(size, 1);
        let b1 = make_buf(size, 2);
        let b2 = make_buf(size, 3);
        let b3 = make_buf(size, 4);

        // NOTE: Throughput is calculated as bytes processed per iteration
        group.throughput(Throughput::Bytes(size as u64));

        // bench 1x
        group.bench_with_input(BenchmarkId::new("crc_1x", size), &b0, |b, buf| {
            b.iter(|| crc.crc(black_box(buf)));
        });

        // bench 2x
        group.bench_with_input(
            BenchmarkId::new("crc_2x", size),
            &(b0.as_slice(), b1.as_slice()),
            |b, (b0, b1)| {
                b.iter(|| crc.crc_2x(black_box([b0, b1])));
            },
        );

        // bench 4x
        group.bench_with_input(
            BenchmarkId::new("crc_4x", size),
            &(b0.as_slice(), b1.as_slice(), b2.as_slice(), b3.as_slice()),
            |b, (b0, b1, b2, b3)| {
                b.iter(|| crc.crc_4x(black_box([b0, b1, b2, b3])));
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_crc_all);
criterion_main!(benches);
