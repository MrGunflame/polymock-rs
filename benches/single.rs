#![feature(test)]

extern crate test;

use polymock::Arena;
use test::Bencher;

#[bench]
fn arena_alloc_1(b: &mut Bencher) {
    let arena = Arena::new(1000);

    b.iter(|| {
        arena.alloc(1);
    });
}

#[bench]
fn arena_alloc_100(b: &mut Bencher) {
    let arena = Arena::new(1000);

    b.iter(|| {
        arena.alloc(100);
    });
}

#[bench]
fn arena_alloc_1000(b: &mut Bencher) {
    let arena = Arena::new(1000);

    b.iter(|| {
        arena.alloc(1000);
    });
}

#[bench]
fn arena_alloc_1500(b: &mut Bencher) {
    let arena = Arena::default();

    b.iter(|| {
        arena.alloc(1500);
    });
}
