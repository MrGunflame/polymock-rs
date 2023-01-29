use core::fmt::{self, Debug, Formatter};
use core::ops::Deref;
use core::ptr::NonNull;
use core::slice;
use core::sync::atomic::{AtomicPtr, Ordering};

use alloc::vec::Vec;

use crate::arena::{ChunkInner, ChunkRef};

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
    pub(crate) ptr: *const u8,
    pub(crate) len: usize,
    data: AtomicPtr<()>,
    vtable: &'static Vtable,
}

impl Bytes {
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if self.len > len {
            self.len = len;
        }
    }

    /// Forces the length of the `Bytes` to `len`.
    ///
    /// Note that the length of `Bytes` is the same as the length of [`BytesMut`].
    ///
    /// # Safety
    ///
    /// The length must not exceed the original length that the `Bytes` was originally allocated
    /// with.
    ///
    /// [`BytesMut`]: crate::BytesMut
    #[inline]
    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    #[inline]
    pub(crate) unsafe fn from_raw_parts(chunk: ChunkRef, ptr: NonNull<u8>, len: usize) -> Self {
        let data = AtomicPtr::new(chunk.leak() as *const _ as *mut ChunkInner as *mut ());

        Bytes {
            ptr: ptr.as_ptr(),
            len,
            data,
            vtable: &CHUNK_VTABLE,
        }
    }

    #[inline]
    fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr, self.len) }
    }
}

impl Clone for Bytes {
    #[inline]
    fn clone(&self) -> Self {
        unsafe { (self.vtable.clone)(&self.data, self.ptr, self.len) }
    }
}

impl Drop for Bytes {
    #[inline]
    fn drop(&mut self) {
        unsafe { (self.vtable.drop)(&self.data, self.ptr, self.len) };
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
            .field("buffer", &self.as_slice())
            .finish()
    }
}

unsafe impl Send for Bytes {}
unsafe impl Sync for Bytes {}

impl PartialEq for Bytes {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Both buffers are equal when they point to the same memory.
        if self.ptr == other.ptr && self.len == other.len {
            true
        } else {
            self.as_slice() == other.as_slice()
        }
    }
}

impl PartialEq<[u8]> for Bytes {
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}

impl Eq for Bytes {}

impl PartialOrd for Bytes {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Bytes {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl PartialOrd<[u8]> for Bytes {
    fn partial_cmp(&self, other: &[u8]) -> Option<core::cmp::Ordering> {
        Some(self.as_slice().cmp(other))
    }
}

pub(crate) struct Vtable {
    /// fn(data, ptr, len)
    clone: unsafe fn(&AtomicPtr<()>, *const u8, usize) -> Bytes,
    /// fn(data, ptr, len)
    to_vec: unsafe fn(&AtomicPtr<()>, *const u8, usize) -> Vec<u8>,
    /// fn(data, ptr, len)
    drop: unsafe fn(&AtomicPtr<()>, *const u8, usize),
}

static CHUNK_VTABLE: Vtable = Vtable {
    clone: chunk_clone,
    to_vec: chunk_to_vec,
    drop: chunk_drop,
};

fn chunk_clone(data: &AtomicPtr<()>, ptr: *const u8, len: usize) -> Bytes {
    let data_ptr = data.load(Ordering::Relaxed);
    let chunk = unsafe { &*(data_ptr as *mut ChunkRef) };

    chunk.increment_reference_count();

    Bytes {
        ptr,
        len,
        data: AtomicPtr::new(data_ptr),
        vtable: &CHUNK_VTABLE,
    }
}

fn chunk_to_vec(data: &AtomicPtr<()>, ptr: *const u8, len: usize) -> Vec<u8> {
    let buf = unsafe { core::slice::from_raw_parts(ptr, len) };
    buf.to_vec()
}

fn chunk_drop(data: &AtomicPtr<()>, ptr: *const u8, len: usize) {
    let chunk_ref = unsafe { &*(data.load(Ordering::Relaxed) as *mut ChunkRef) };

    let old_rc = chunk_ref.ref_count.fetch_sub(1, Ordering::Release);
    if old_rc != 1 {
        return;
    }

    chunk_ref.ref_count.load(Ordering::Acquire);

    // Take ownership of the chunk.
    // SAFETY: The chunk was leaked once first created. A call to `chunk_drop` means
    // that the last reference of this `Bytes` was dropped.
    let chunk = unsafe { chunk_ref.copy() };

    drop(chunk);
}

#[cfg(all(not(loom), test))]
mod tests {
    use std::sync::atomic::Ordering;

    use super::Bytes;
    use crate::arena::ChunkRef;

    #[test]
    fn test_bytes() {
        let chunk = ChunkRef::new(1000);
        let ptr = chunk.alloc(100).unwrap();

        assert_eq!(chunk.ref_count.load(Ordering::Relaxed), 1);

        let bytes = unsafe { Bytes::from_raw_parts(chunk.clone(), ptr, 100) };

        // assert_eq!(bytes.chunk, chunk);
        assert_eq!(bytes.len, 100);

        assert_eq!(chunk.ref_count.load(Ordering::Relaxed), 2);

        let bytes2 = bytes.clone();
        assert_eq!(bytes.ptr, bytes2.ptr);
        assert_eq!(bytes.len, bytes2.len);

        assert_eq!(chunk.ref_count.load(Ordering::Relaxed), 3);

        drop(bytes);
        assert_eq!(chunk.ref_count.load(Ordering::Relaxed), 2);

        drop(bytes2);
        assert_eq!(chunk.ref_count.load(Ordering::Relaxed), 1);
    }
}

#[cfg(all(test, loom))]
mod loom_tests {
    use std::vec::Vec;

    use loom::sync::atomic::Ordering;
    use loom::thread;

    use super::Bytes;
    use crate::arena::ChunkRef;

    const THREADS: usize = 2;
    const ITERATIONS: usize = 20;

    #[test]
    fn test_bytes() {
        loom::model(|| {
            let chunk = ChunkRef::new(1000);
            let ptr = chunk.alloc(100).unwrap();
            let bytes = unsafe { Bytes::from_raw_parts(chunk.clone(), ptr, 100) };

            let threads: Vec<_> = (0..THREADS)
                .map(|_| {
                    let bytes = bytes.clone();

                    thread::spawn(move || {
                        let mut bufs = Vec::with_capacity(ITERATIONS);

                        for _ in 0..ITERATIONS {
                            bufs.push(bytes.clone());
                        }

                        for buf in bufs.into_iter() {
                            drop(buf);
                        }
                    })
                })
                .collect();

            for th in threads {
                th.join().unwrap();
            }

            assert_eq!(chunk.ref_count.load(Ordering::Relaxed), 2);
        });
    }
}
