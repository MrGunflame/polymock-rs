use core::alloc::Layout;
use core::ops::Deref;
use core::ptr::NonNull;

use std::sync::RwLock;

use crate::bytes_mut::BytesMut;
use crate::loom::sync::atomic::{AtomicUsize, Ordering};

pub const PAGE: usize = u16::MAX as usize;

#[derive(Debug)]
pub struct Arena {
    chunk_size: usize,
    chunks: RwLock<Vec<ChunkRef>>,
}

impl Arena {
    pub fn new(chunk_size: usize) -> Self {
        Self {
            chunk_size,
            chunks: RwLock::new(Vec::new()),
        }
    }

    pub fn alloc(&self, size: usize) -> BytesMut {
        let (chunk, ptr) = self.alloc_raw(size);

        unsafe { BytesMut::from_raw_parts(chunk, ptr, size) }
    }

    pub fn zeroed(&self, size: usize) -> BytesMut {
        let (chunk, ptr) = self.alloc_raw(size);

        unsafe {
            std::ptr::write_bytes(ptr.as_ptr(), 0, size);
        }

        unsafe { BytesMut::from_raw_parts(chunk, ptr, size) }
    }

    fn alloc_raw(&self, size: usize) -> (ChunkRef, NonNull<u8>) {
        if size > self.chunk_size {
            panic!("cannot allocate larger than chunk size");
        }

        let chunks = self.chunks.read().unwrap();
        for chunk in &*chunks {
            if chunk.ref_count.load(Ordering::Relaxed) == 1 {
                unsafe {
                    chunk.reset();
                }
            }

            if let Some(ptr) = chunk.alloc(size) {
                return (chunk.clone(), ptr);
            }
        }

        drop(chunks);

        let chunk = ChunkRef::new(self.chunk_size);
        let ch = chunk.clone();
        let ptr = chunk.alloc(size).unwrap();

        let mut chunks = self.chunks.write().unwrap();
        chunks.push(chunk);

        (ch, ptr)
    }
}

impl Default for Arena {
    #[inline]
    fn default() -> Self {
        Self::new(PAGE)
    }
}

#[derive(Debug)]
pub(crate) struct ChunkRef {
    ptr: NonNull<ChunkInner>,
}

impl ChunkRef {
    #[inline]
    pub unsafe fn copy(&self) -> Self {
        unsafe { std::ptr::read(self as *const Self) }
    }

    #[inline]
    fn new(size: usize) -> Self {
        let boxed = Box::new(ChunkInner::new(size));
        let ptr = unsafe { NonNull::new_unchecked(Box::leak(boxed) as *mut ChunkInner) };

        Self { ptr }
    }
}

impl Deref for ChunkRef {
    type Target = ChunkInner;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

impl Clone for ChunkRef {
    #[inline]
    fn clone(&self) -> Self {
        let old_rc = self.ref_count.fetch_add(1, Ordering::Relaxed);

        if old_rc > usize::MAX >> 1 {
            crate::abort();
        }

        Self { ptr: self.ptr }
    }
}

impl Drop for ChunkRef {
    #[inline]
    fn drop(&mut self) {
        let old_rc = self.ref_count.fetch_sub(1, Ordering::Release);

        if old_rc != 1 {
            return;
        }

        self.ref_count.load(Ordering::Acquire);

        unsafe {
            drop(Box::from_raw(self.ptr.as_ptr()));
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
    ref_count: AtomicUsize,
}

impl ChunkInner {
    fn new(size: usize) -> Self {
        let layout = Layout::array::<u8>(size).unwrap();

        let ptr = unsafe { alloc::alloc::alloc(layout) };
        assert!(!ptr.is_null());

        Self {
            layout,
            ptr,
            head: AtomicUsize::new(0),
            ref_count: AtomicUsize::new(1),
        }
    }

    fn alloc(&self, size: usize) -> Option<NonNull<u8>> {
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

    #[inline]
    unsafe fn reset(&self) {
        self.head.store(0, Ordering::Release);
    }
}

impl Drop for ChunkInner {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            alloc::alloc::dealloc(self.ptr, self.layout);
        }
    }
}

#[cfg(all(not(loom), test))]
mod tests {
    use std::sync::Arc;
    use std::thread;

    use super::ChunkRef;
    use crate::loom::sync::atomic::Ordering;
    use crate::Arena;

    const THREADS: usize = 4;
    const ITERATIONS: usize = 100_000;

    #[test]
    fn test_chunk() {
        let chunk = ChunkRef::new(4000);
        assert_eq!(chunk.head.load(Ordering::Acquire), 0);

        chunk.alloc(1000).unwrap();
        assert_eq!(chunk.head.load(Ordering::Acquire), 1000);

        chunk.alloc(1000).unwrap();
        assert_eq!(chunk.head.load(Ordering::Acquire), 2000);

        chunk.alloc(1000).unwrap();
        assert_eq!(chunk.head.load(Ordering::Acquire), 3000);

        chunk.alloc(1000).unwrap();
        assert_eq!(chunk.head.load(Ordering::Acquire), 4000);

        assert!(chunk.alloc(1).is_none());
    }

    #[test]
    fn test_chunk_threads() {
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

        let threads: Vec<_> = (0..THREADS)
            .map(|_| {
                let arena = arena.clone();
                thread::spawn(move || {
                    arena.zeroed(1);
                })
            })
            .collect();

        for th in threads {
            th.join().unwrap();
        }
    }
}

#[cfg(all(loom, test))]
mod loom_tests {
    use loom::thread;

    use super::ChunkRef;
    use crate::loom::sync::atomic::Ordering;

    const THREADS: usize = 2;
    const ITERATIONS: usize = 20;

    #[test]
    fn test_chunk() {
        loom::model(|| {
            let mut chunk = ChunkRef::new(1_000_000);

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

            // assert_eq!(chunk.head.load(Ordering::Relaxed), THREADS * ITERATIONS);
        });
    }
}
