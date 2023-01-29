//! A fast thread-safe bump allocation arena.
//!
//! `polymock` provides a fast allocation [`Arena`] using the bump allocation strategy. It's
//! primary use case is high-throughput multi-threaded network applications which allocate and free
//! buffers very frequently and cannot afford going through the global allocator.
//!
//! `polymock` only supports allocating `[u8]` buffers. It will never support allocating of
//! different objects.
//!
//! # Using `bytes`
//!
//! `polymock` provides it's own [`Bytes`] type that is a mostly drop-in replacement for the
//! equivalent type from the [`bytes`] crate.
//!
//! Once the construction using a custom vtable will be public, [`Bytes`] will be deprecated in
//! favor of the [`bytes`] crate.
//!
//! # `no_std` support
//!
//! `polymock` supports `no_std`, but requires the `alloc` crate. To enable `no_std` support
//! disable the default "std" feature:
//!
//! ```toml
//! polymock = { version = "0.2.0", default-features = false }
//! ```
//!
//! # Example
//!
//! ```
//! use polymock::Arena;
//!
//! let mut arena = Arena::default();
//!
//! let mut buf = arena.alloc(1500);
//!
//! for b in buf.iter_mut() {
//!     *b = 1;
//! }
//!
//! let buf1 = buf.freeze();
//! let buf2 = buf1.clone();
//!
//! assert_eq!(buf1, buf2);
//! ```
//!
//! [`bytes`]: https://docs.rs/bytes/latest/bytes/index.html

#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

extern crate alloc;

#[cfg(any(feature = "std", test))]
extern crate std;

pub mod buf;

pub(crate) mod arena;
pub(crate) mod bytes;
pub(crate) mod bytes_mut;
pub(crate) mod loom;

pub use arena::Arena;
pub use buf::Buf;
pub use bytes::Bytes;
pub use bytes_mut::BytesMut;

#[inline(never)]
#[cold]
pub(crate) fn abort() -> ! {
    #[cfg(feature = "std")]
    {
        std::process::abort();
    }

    #[cfg(not(feature = "std"))]
    {
        struct Abort;
        impl Drop for Abort {
            fn drop(&mut self) {
                panic!();
            }
        }

        panic!("abort");
    }
}
