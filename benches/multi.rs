#![feature(test)]

use std::sync::Arc;
use std::thread;

use polymock::Arena;
use test::Bencher;

extern crate test;

#[bench]
fn arena_alloc_100(b: &mut Bencher) {
    b.iter(|| {
        let arena = Arc::new(Arena::new(1000));

        let threads: Vec<_> = (0..4)
            .map(|_| {
                let arena = arena.clone();

                thread::spawn(move || {
                    for _ in 0..1000 {
                        arena.alloc(100);
                    }
                })
            })
            .collect();

        for th in threads {
            th.join().unwrap();
        }
    });
}
