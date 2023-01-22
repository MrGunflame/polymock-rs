# polymock

[![Crates.io](https://img.shields.io/crates/v/polymock)](https://crates.io/crates/polymock)
[![Docs.rs](https://img.shields.io/docsrs/polymock/latest)](https://docs.rs/polymock)

A thread-safe bump allocation arena for bytes.

`polymock` is primarly targeted at high-throughput multi-threaded network applications which
need to allocate and free buffers very frequently and cannot afford going through the global
allocator.

## Usage

Add `polymock` to your `Cargo.toml`:

```toml
polymock = "0.2.0"
```

Next create an allocation arena and allocate some buffers:

```rustt
use polymock::Arena;

// Create a bump arena with a chunk size of 1000 bytes.
let arena = Arena::new(1000);

let mut buffers = Vec::new();
for _ in 0..10 {
    // All 10 buffers will be allocated in the same chunk.
    let buf = arena.alloc();

    buffers.push(buf);
}

// The allocated buffers may outlive the arena they
// were allocated with.

drop(arena);

buffers[0][0] = 1;
```

# License

Licensed under either [MIT License](https://github.com/MrGunflame/polymock-rs/blob/master/LICENSE-MIT) or [Apache License, Version 2.0](https://github.com/MrGunflame/polymock-rs/blob/master/LICENSE-APACHE) at your option.
