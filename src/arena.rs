use core::alloc::Layout;
use core::mem;
use core::ops::Deref;
use core::ptr::{self, NonNull};
use core::sync::atomic::AtomicPtr;

use alloc::boxed::Box;

use crate::bytes_mut::BytesMut;
use crate::loom::sync::atomic::{AtomicUsize, Ordering};

pub const PAGE: usize = u16::MAX as usize;

/// A bump allocation arena.
///
/// # Examples
///
/// ```
/// # use polymock::Arena;
/// #
/// let mut arena = Arena::new(1000);
///
///
/// let mut buffers = Vec::new();
/// for _ in 0..10 {
///     // All 10 buffers will be allocated in the same chunk.
///     let mut buf = arena.alloc(100);
///
///     buffers.push(buf);
/// }
///
/// // The buffers may outlive the arena they were allocated with.
/// drop(arena);
///
/// buffers[0][0] = 1;
/// ```
///
#[derive(Debug)]
pub struct Arena {
    chunk_size: usize,
    head: AtomicPtr<ChunkInner>,
}

impl Arena {
    /// Creates a new `Arena` using the given `chunk_size` for every allocated chunk.
    ///
    /// # Panics
    ///
    /// Panics if `chunk_size` is bigger than `isize::MAX`.
    pub fn new(chunk_size: usize) -> Self {
        // We cannot allocated more than isize::MAX so allowing this would only
        // result in the first chunk allocation to fail.
        if chunk_size > usize::MAX >> 1 {
            panic!("cannot create arena with bigger than isize::MAX chunk_size");
        }

        Self {
            chunk_size,
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// Allocates a new [`BytesMut`] from the `Arena`.
    ///
    /// Note that the returned [`BytesMut`] may contain previously used buffers. If you need to
    /// create a zeroed [`BytesMut`], consider using [`zeroed`].
    ///
    /// [`zeroed`]: Self::zeroed
    #[inline]
    pub fn alloc(&self, size: usize) -> BytesMut {
        let (chunk, ptr) = self.alloc_raw(size);

        unsafe { BytesMut::from_raw_parts(chunk, ptr, size) }
    }

    /// Allocates a new, zeroed [`BytesMut`] from the `Arena`.
    ///
    /// Note that `zeroed` zeroes the returned [`BytesMut`]. If that's not necessary you may want
    /// to use [`alloc`], which does not zero the returned [`BytesMut`].
    ///
    /// [`alloc`]: Self::alloc
    #[inline]
    pub fn zeroed(&self, size: usize) -> BytesMut {
        let mut buf = self.alloc(size);

        unsafe {
            ptr::write_bytes(buf.as_mut_ptr(), 0, size);
        }

        buf
    }

    fn alloc_raw(&self, size: usize) -> (ChunkRef, NonNull<u8>) {
        if size > self.chunk_size {
            panic!("cannot allocate larger than chunk size");
        }

        let mut next = self.head.load(Ordering::SeqCst);
        loop {
            if next.is_null() {
                break;
            }

            let chunk = unsafe { &*next };

            // If the arena has the only reference to the chunk, it may be reused
            // for future operations.
            if chunk.ref_count.load(Ordering::SeqCst) == 1 {
                // SAFETY: The arena has the only reference to the chunk. There are
                // not references to the memory buffer of the chunk.
                unsafe {
                    chunk.reset();
                }
            }

            if let Some(ptr) = chunk.alloc(size) {
                // Construct a `ChunkRef` manually from its base pointer.
                let chunk = unsafe { ChunkRef::from_ptr(next) };
                chunk.increment_reference_count();

                return (chunk, ptr);
            }

            // Next chunk.
            next = chunk.next.load(Ordering::SeqCst);
        }

        // Allocate and append a new chunk.
        let chunk = ChunkRef::new(self.chunk_size);
        let ch = chunk.clone();
        let ptr = chunk.alloc(size).unwrap();

        // Find the tail chunk, i.e. the last chunk in the linked list.
        let mut tail = &self.head;
        loop {
            let chunk_ptr = chunk.inner.as_ptr();

            let tail_ptr = tail.load(Ordering::SeqCst);
            if !tail_ptr.is_null() {
                // Tail is not null.
                tail = unsafe { &(*tail_ptr).next };
                continue;
            }

            // tail_ptr is the tail.
            // FIXME: Can this effectively be replaced with an compare_exchange_weak?
            let Err(tail_ptr) = tail
                .compare_exchange(
                    ptr::null_mut(),
                    chunk_ptr,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                )
            else {
                break;
            };

            // Tail is not null.
            tail = unsafe { &(*tail_ptr).next };
        }

        // We store the pointer to the chunk manually.
        // Do not decrement the reference count.
        core::mem::forget(chunk);

        (ch, ptr)
    }
}

impl Default for Arena {
    #[inline]
    fn default() -> Self {
        Self::new(PAGE)
    }
}

/// A reference to a [`ChunkInner`], similar to an [`Arc`].
///
/// [`Arc`]: alloc::sync::Arc
#[derive(Debug, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct ChunkRef {
    inner: NonNull<ChunkInner>,
}

impl ChunkRef {
    /// Copies the `ChunkRef` without incrementing the reference count.
    ///
    /// # Safety
    ///
    /// This function does not go through the [`Clone`] implementation of `ChunkRef`, but the
    /// copied value will still be dropped as normal. If both `ChunkRef`s will be dropped normally
    /// the underlying backing store **will be freed twice, resulting in undefined behavior.**
    #[inline]
    pub unsafe fn copy(&self) -> Self {
        // SAFETY: `self` is always a valid, initialized and aligned reference.
        // `ChunkRef` can be safely be copied as `NonNull` is `Copy`.
        unsafe { ptr::read(self as *const Self) }
    }

    /// Manually constructs a `ChunkRef` from its underlying [`ChunkInner`] pointer.
    ///
    /// **Note that `from_ptr` does not increment the reference count.**
    ///
    /// # Safety
    ///
    /// `ptr` must not be null and must point to a valid [`ChunkInner`] instance.
    #[inline]
    pub unsafe fn from_ptr(ptr: *mut ChunkInner) -> Self {
        debug_assert!(!ptr.is_null());

        Self {
            // SAFETY: The caller guarantees that `ptr` is not null.
            inner: unsafe { NonNull::new_unchecked(ptr) },
        }
    }

    /// Creates a new `ChunkRef` with a new underlying chunk with the given `size`.
    #[inline]
    pub(crate) fn new(size: usize) -> Self {
        let boxed = Box::new(ChunkInner::new(size));
        let ptr = NonNull::from(Box::leak(boxed));

        Self { inner: ptr }
    }
}

impl Deref for ChunkRef {
    type Target = ChunkInner;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.inner.as_ref() }
    }
}

impl Clone for ChunkRef {
    #[inline]
    fn clone(&self) -> Self {
        let old_rc = self.ref_count.fetch_add(1, Ordering::Relaxed);

        // Since leaking elements is a safe operation, we must make sure to
        // NEVER overflow the reference count.
        if old_rc > usize::MAX >> 1 {
            crate::abort();
        }

        Self { inner: self.inner }
    }
}

impl Drop for ChunkRef {
    #[inline]
    fn drop(&mut self) {
        let old_rc = self.ref_count.fetch_sub(1, Ordering::Release);

        if old_rc != 1 {
            return;
        }

        // Fence to prevent reordering of data access after deletion.
        // Synchronizes with the Release load.
        self.ref_count.load(Ordering::Acquire);

        // SAFETY: We've had the last reference to the underlying value.
        unsafe {
            drop(Box::from_raw(self.inner.as_ptr()));
        }
    }
}

unsafe impl Send for ChunkRef {}
unsafe impl Sync for ChunkRef {}

#[derive(Debug)]
pub(crate) struct ChunkInner {
    layout: Layout,
    ptr: *mut u8,
    head: AtomicUsize,
    pub(crate) ref_count: AtomicUsize,
    /// Pointer to the next chunk.
    next: AtomicPtr<Self>,
}

impl ChunkInner {
    /// Creates a new `ChunkInner` with the given `size`.
    fn new(size: usize) -> Self {
        if cfg!(debug_assertions) {
            Layout::array::<u8>(size).unwrap();
        }

        let size = mem::size_of::<u8>() * size;
        let align = mem::align_of::<u8>();

        // SAFETY: The arena chunk size must never exceed `isize::MAX` and the size of
        // `u8` is 1 so the size cannot overflow.
        let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

        let ptr = unsafe { alloc::alloc::alloc(layout) };
        assert!(!ptr.is_null());

        Self {
            layout,
            ptr,
            head: AtomicUsize::new(0),
            ref_count: AtomicUsize::new(1),
            next: AtomicPtr::new(core::ptr::null_mut()),
        }
    }

    pub(crate) fn alloc(&self, size: usize) -> Option<NonNull<u8>> {
        let mut head = self.head.load(Ordering::Acquire);

        if head + size > self.layout.size() {
            return None;
        }

        while let Err(curr) =
            self.head
                .compare_exchange_weak(head, head + size, Ordering::SeqCst, Ordering::SeqCst)
        {
            head = curr;

            if head + size > self.layout.size() {
                return None;
            }
        }

        unsafe { Some(NonNull::new_unchecked(self.ptr.add(head))) }
    }

    /// Force the head of the chunk back to the start.
    ///
    /// # Safety
    ///
    /// This is only safe to call if there are no references to the chunk that access the buffer,
    /// mutably and immutably. If this condition is violated, buffers may overlap resulting in
    /// undefined behavior.
    #[inline]
    unsafe fn reset(&self) {
        self.head.store(0, Ordering::Release);
    }

    /// Increments the reference count on the `ChunkInner` by one.
    #[inline]
    fn increment_reference_count(&self) {
        self.ref_count.fetch_add(1, Ordering::Relaxed);
    }
}

impl Drop for ChunkInner {
    #[inline]
    fn drop(&mut self) {
        // SAFETY: The given pointer and layout were previously used to allocate the memory.
        unsafe {
            alloc::alloc::dealloc(self.ptr, self.layout);
        }
    }
}

#[cfg(all(not(loom), test))]
mod tests {
    use std::ptr::NonNull;
    use std::sync::{mpsc, Arc};
    use std::thread;
    use std::vec::Vec;

    use super::ChunkRef;
    use crate::loom::sync::atomic::Ordering;
    use crate::{Arena, BytesMut};

    const THREADS: usize = 4;
    const ITERATIONS: usize = 100_000;

    struct SendNonNull(NonNull<u8>);

    unsafe impl Send for SendNonNull {}

    impl From<NonNull<u8>> for SendNonNull {
        fn from(value: NonNull<u8>) -> Self {
            Self(value)
        }
    }

    #[test]
    fn test_chunk() {
        let chunk = ChunkRef::new(4000);
        assert_eq!(chunk.head.load(Ordering::Acquire), 0);

        let ptr = chunk.alloc(1000).unwrap();
        assert_eq!(ptr.as_ptr() as usize, chunk.ptr as usize);
        assert_eq!(chunk.head.load(Ordering::Acquire), 1000);

        let ptr = chunk.alloc(1000).unwrap();
        assert_eq!(ptr.as_ptr() as usize, chunk.ptr as usize + 1000);
        assert_eq!(chunk.head.load(Ordering::Acquire), 2000);

        let ptr = chunk.alloc(1000).unwrap();
        assert_eq!(ptr.as_ptr() as usize, chunk.ptr as usize + 2000);
        assert_eq!(chunk.head.load(Ordering::Acquire), 3000);

        let ptr = chunk.alloc(1000).unwrap();
        assert_eq!(ptr.as_ptr() as usize, chunk.ptr as usize + 3000);
        assert_eq!(chunk.head.load(Ordering::Acquire), 4000);

        assert!(chunk.alloc(1).is_none());
    }

    #[test]
    fn test_chunk_threads() {
        let chunk = ChunkRef::new(1_000_000);

        let (tx, rx) = mpsc::channel::<Vec<SendNonNull>>();

        let threads: Vec<_> = (0..THREADS)
            .map(|_| {
                let chunk = chunk.clone();
                let tx = tx.clone();
                thread::spawn(move || {
                    let mut ptrs = Vec::<SendNonNull>::with_capacity(ITERATIONS);

                    for _ in 0..ITERATIONS {
                        let ptr = chunk.alloc(1).unwrap();

                        ptrs.push(ptr.into());
                    }

                    tx.send(ptrs).unwrap();
                })
            })
            .collect();

        drop(tx);

        for th in threads {
            th.join().unwrap();
        }

        let mut ptrs = Vec::with_capacity(THREADS * ITERATIONS);

        while let Ok(vec) = rx.recv() {
            ptrs.extend(vec);
        }

        for (index, ptr) in ptrs.iter().enumerate() {
            for (index2, ptr2) in ptrs.iter().enumerate() {
                if index == index2 {
                    continue;
                }

                if ptr.0 == ptr2.0 {
                    panic!("[{}] [{}] duplicate pointer: {:p}", index, index2, ptr.0);
                }
            }
        }

        assert_eq!(chunk.head.load(Ordering::Relaxed), THREADS * ITERATIONS);
    }

    #[test]
    fn test_arena() {
        let arena = Arena::new(4000);

        for _ in 0..4000 * 4 {
            arena.zeroed(1);
        }
    }

    #[test]
    fn test_arena_threads() {
        let arena = Arc::new(Arena::new(1_000));

        let (tx, rx) = mpsc::channel::<Vec<BytesMut>>();

        let threads: Vec<_> = (0..THREADS)
            .map(|_| {
                let arena = arena.clone();
                let tx = tx.clone();
                thread::spawn(move || {
                    let mut bufs = Vec::<BytesMut>::with_capacity(ITERATIONS);

                    for _ in 0..ITERATIONS {
                        let buf = arena.zeroed(1);

                        bufs.push(buf);
                    }

                    tx.send(bufs).unwrap();
                })
            })
            .collect();

        drop(tx);

        for th in threads {
            th.join().unwrap();
        }

        let mut bufs = Vec::with_capacity(THREADS * ITERATIONS);
        while let Ok(vec) = rx.recv() {
            bufs.extend(vec);
        }

        for (index, buf) in bufs.iter().enumerate() {
            for (index2, buf2) in bufs.iter().enumerate() {
                if index == index2 {
                    continue;
                }

                let ptr = buf.as_ptr();
                let ptr2 = buf2.as_ptr();

                if ptr == ptr2 {
                    panic!("[{}] [{}] duplicate pointer: {:p}", index, index2, ptr);
                }
            }
        }
    }
}

#[cfg(all(loom, test))]
mod loom_tests {
    use std::vec::Vec;

    use loom::sync::atomic::Ordering;
    use loom::thread;

    use super::ChunkRef;

    const THREADS: usize = 2;
    const ITERATIONS: usize = 20;

    #[test]
    fn test_chunk() {
        loom::model(|| {
            let chunk = ChunkRef::new(1_000_000);

            let threads: Vec<_> = (0..THREADS)
                .map(|_| {
                    let chunk = chunk.clone();
                    thread::spawn(move || {
                        for _ in 0..ITERATIONS {
                            chunk.alloc(1).unwrap();
                        }
                    })
                })
                .collect();

            for th in threads {
                th.join().unwrap();
            }

            assert_eq!(chunk.head.load(Ordering::Relaxed), THREADS * ITERATIONS);
        });
    }
}
