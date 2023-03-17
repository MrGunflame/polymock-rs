#![feature(test)]

use test::{black_box, Bencher};

extern crate test;

#[bench]
fn bench_global_1500(b: &mut Bencher) {
    b.iter(|| {
        black_box(Vec::<u8>::with_capacity(1500));
    });
}

#[bench]
fn bench_global_chunks(b: &mut Bencher) {
    b.iter(|| {
        for _ in 0..1000 {
            black_box({
                let buf: Vec<u8> = Vec::with_capacity(100);
                buf.leak();
            });
        }
    });
}
