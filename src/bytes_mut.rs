use core::fmt::{self, Debug, Formatter};
use core::mem;
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;
use core::slice;

use crate::arena::ChunkRef;
use crate::bytes::Bytes;

/// A unique view into a fixed size slice of memory allocated by an [`Arena`].
///
/// Unlike other collections, `BytesMut` cannot grow. The exact wanted size must be known at time
/// of creation. This allows `BytesMut` to share it's memory region with other buffers without
/// risking growing over them.
pub struct BytesMut {
    chunk: ChunkRef,
    ptr: NonNull<u8>,
    len: usize,
}

impl BytesMut {
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Shortens the `BytesMut` to `len`.
    ///
    /// If `len` is greater than the current buffer, this has no effect.
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if self.len > len {
            unsafe {
                self.set_len(len);
            }
        }
    }

    /// Forces the length of the `BytesMut` to `len`.
    ///
    /// Consider [`truncate`] for a safe alternative.
    ///
    /// # Safety
    ///
    /// The new length must not exceed the length that the `BytesMut` was originally allocated with.
    ///
    /// [`truncate`]: Self::truncate
    #[inline]
    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    pub fn freeze(self) -> Bytes {
        let chunk = unsafe { self.chunk.copy() };
        let ptr = self.ptr;
        let len = self.len;

        // Do not decrement the reference count.
        mem::forget(self);

        unsafe { Bytes::from_raw_parts(chunk, ptr, len) }
    }

    #[inline]
    pub(crate) unsafe fn from_raw_parts(chunk: ChunkRef, ptr: NonNull<u8>, len: usize) -> Self {
        Self { chunk, ptr, len }
    }

    #[inline]
    fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }

    #[inline]
    fn as_slice_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}

impl Deref for BytesMut {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl AsRef<[u8]> for BytesMut {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl DerefMut for BytesMut {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_slice_mut()
    }
}

impl Debug for BytesMut {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("BytesMut")
            .field("chunk", &self.chunk)
            .field("buffer", &self.as_slice())
            .finish()
    }
}

unsafe impl Send for BytesMut {}
unsafe impl Sync for BytesMut {}
