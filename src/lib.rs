#![deny(unsafe_op_in_unsafe_fn)]

extern crate alloc;

pub(crate) mod arena;
pub(crate) mod bytes;
pub(crate) mod bytes_mut;
pub(crate) mod loom;

pub use arena::Arena;
pub use bytes::Bytes;
pub use bytes_mut::BytesMut;

pub(crate) fn abort() {
    std::process::abort();
}
