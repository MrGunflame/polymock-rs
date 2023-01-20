use core::fmt::{self, Debug, Formatter};
use core::ops::Deref;
use core::ptr::NonNull;
use core::slice;

use crate::arena::ChunkRef;

/// A cheaply cloneable view into a slice of memory allocated by an [`Arena`].
///
/// `Bytes` is a mostly drop-in replacement for [`Bytes`] from the [`bytes`] crate and behaves the
/// same internally.
///
/// `Bytes` is expected to be deprecated once the `bytes` crate allows creating a [`Bytes`]
/// values using a custom vtable.
///
/// [`Bytes`]: https://docs.rs/bytes/latest/bytes/struct.Bytes.html
/// [`bytes`]: https://docs.rs/bytes/latest/bytes/index.html
/// [`Arena`]: crate::Arena
pub struct Bytes {
    chunk: ChunkRef,
    ptr: NonNull<u8>,
    len: usize,
}

impl Bytes {
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if self.len > len {
            self.len = len;
        }
    }

    #[inline]
    pub(crate) unsafe fn from_raw_parts(chunk: ChunkRef, ptr: NonNull<u8>, len: usize) -> Self {
        Self { chunk, ptr, len }
    }

    #[inline]
    fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl Deref for Bytes {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl AsRef<[u8]> for Bytes {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl Debug for Bytes {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Bytes")
            .field("chunk", &self.chunk)
            .field("buffer", &self.as_slice())
            .finish()
    }
}

unsafe impl Send for Bytes {}
unsafe impl Sync for Bytes {}
