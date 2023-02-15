#![feature(test)]

use test::{black_box, Bencher};

extern crate test;

#[bench]
fn bench_global_1500(b: &mut Bencher) {
    b.iter(|| {
        black_box(Vec::<u8>::with_capacity(1500));
    });
}
