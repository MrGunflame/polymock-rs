//! A fast thread-safe bump allocation arena.
//!
//! `polymock` provides a fast allocation [`Arena`] using the bump allocation strategy. It's
//! primary use case is high-throughput multi-threaded network applications which allocate and free
//! buffers very frequently and cannot allow going through the global allocator.
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
//! let buf2 = buf.freeze();
//!
//! assert_eq!(buf1, buf2);
//! ```
//!
//! [`bytes`]: https://docs.rs/bytes/latest/bytes/index.html

#![deny(unsafe_op_in_unsafe_fn)]

extern crate alloc;

pub(crate) mod arena;
pub(crate) mod bytes;
pub(crate) mod bytes_mut;
pub(crate) mod loom;

pub use arena::Arena;
pub use bytes::Bytes;
pub use bytes_mut::BytesMut;

#[inline(never)]
#[cold]
pub(crate) fn abort() -> ! {
    std::process::abort();
}
