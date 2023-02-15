use crate::bytes::Bytes;

macro_rules! get_buf_impl {
    ($src:expr,$t:ty, $f:path) => {{
        let mut buf = [0; std::mem::size_of::<$t>()];
        $src.copy_to_slice(&mut buf);
        $f(buf)
    }};
}

use alloc::vec::Vec;
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub use reader::Reader;

/// A readable memory buffer.
///
/// `Buf` is a cursor to a readable memory buffer. It exposes functions to read and move the cursor
/// forward.
///
/// This is a mostly drop-in replacement for [`bytes::Buf`]. `Buf` will be deprecated once the
/// `bytes` crate can be used with custom vtables. See crate level docs for more details.
///
/// [`bytes::Buf`]: https://docs.rs/bytes/latest/bytes/trait.Buf.html
pub trait Buf {
    /// Advances the cursor of the buffer by `cnt` bytes.
    fn advance(&mut self, cnt: usize);

    /// Returns a slice, starting at the current position and a length of `Buf::remaining()`.
    fn chunk(&self) -> &[u8];

    /// Returns the number of remaining bytes in the buffer.
    fn remaining(&self) -> usize;

    /// Consumes and Returns the first `len` as a [`Bytes`].
    fn copy_to_bytes(&mut self, len: usize) -> Bytes {
        assert!(len <= self.remaining());

        let mut rem = len;
        let mut buf = Vec::with_capacity(len);
        while rem > 0 {
            let chunk = self.chunk();

            let cnt = core::cmp::min(chunk.len(), rem);
            buf.extend(&chunk[..cnt]);

            rem -= cnt;
            self.advance(cnt);
        }

        buf.into()
    }

    /// Copy bytes from the buffer into `dst`.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < dst.len()`.
    #[inline]
    fn copy_to_slice(&mut self, dst: &mut [u8]) {
        let mut off = 0;

        assert!(self.remaining() >= dst.len());

        while off < dst.len() {
            let cnt;

            let src = self.chunk();
            cnt = core::cmp::min(src.len(), dst.len() - off);

            unsafe {
                core::ptr::copy_nonoverlapping(src.as_ptr(), dst[off..].as_mut_ptr(), cnt);
            }

            off += cnt;
            self.advance(cnt);
        }
    }

    /// Takes an `f32` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 4`.
    #[inline]
    fn get_f32(&mut self) -> f32 {
        get_buf_impl!(self, f32, f32::from_be_bytes)
    }

    /// Takes an `f32` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 4`.
    #[inline]
    fn get_f32_le(&mut self) -> f32 {
        get_buf_impl!(self, f32, f32::from_le_bytes)
    }

    /// Takes an `f32` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 4`.
    #[inline]
    fn get_f32_ne(&mut self) -> f32 {
        get_buf_impl!(self, f32, f32::from_ne_bytes)
    }

    /// Takes an `f64` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 8`.
    #[inline]
    fn get_f64(&mut self) -> f64 {
        get_buf_impl!(self, f64, f64::from_be_bytes)
    }

    /// Takes an `f64` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 8`.
    #[inline]
    fn get_f64_le(&mut self) -> f64 {
        get_buf_impl!(self, f64, f64::from_le_bytes)
    }

    /// Takes an `f64` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 8`.
    #[inline]
    fn get_f64_ne(&mut self) -> f64 {
        get_buf_impl!(self, f64, f64::from_ne_bytes)
    }

    /// Takes an `u8` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 1`.
    #[inline]
    fn get_u8(&mut self) -> u8 {
        get_buf_impl!(self, u8, u8::from_be_bytes)
    }

    /// Takes an `u8` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 1`.
    #[inline]
    fn get_u8_le(&mut self) -> u8 {
        get_buf_impl!(self, u8, u8::from_le_bytes)
    }

    /// Takes an `u8` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 1`.
    #[inline]
    fn get_u8_ne(&mut self) -> u8 {
        get_buf_impl!(self, u8, u8::from_ne_bytes)
    }

    /// Takes an `u16` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 2`.
    #[inline]
    fn get_u16(&mut self) -> u16 {
        get_buf_impl!(self, u16, u16::from_be_bytes)
    }

    /// Takes an `u16` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 2`.
    #[inline]
    fn get_u16_le(&mut self) -> u16 {
        get_buf_impl!(self, u16, u16::from_le_bytes)
    }

    /// Takes an `u16` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 2`.
    #[inline]
    fn get_u16_ne(&mut self) -> u16 {
        get_buf_impl!(self, u16, u16::from_ne_bytes)
    }

    /// Takes an `u32` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 4`.
    #[inline]
    fn get_u32(&mut self) -> u32 {
        get_buf_impl!(self, u32, u32::from_be_bytes)
    }

    /// Takes an `u32` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 4`.
    #[inline]

    fn get_u32_le(&mut self) -> u32 {
        get_buf_impl!(self, u32, u32::from_le_bytes)
    }

    /// Takes an `u32` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 4`.
    #[inline]
    fn get_u32_ne(&mut self) -> u32 {
        get_buf_impl!(self, u32, u32::from_ne_bytes)
    }

    /// Takes an `u64` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 8`.
    #[inline]
    fn get_u64(&mut self) -> u64 {
        get_buf_impl!(self, u64, u64::from_be_bytes)
    }

    /// Takes an `u64` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 8`.
    #[inline]
    fn get_u64_le(&mut self) -> u64 {
        get_buf_impl!(self, u64, u64::from_le_bytes)
    }

    /// Takes an `u64` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 8`.
    #[inline]
    fn get_u64_ne(&mut self) -> u64 {
        get_buf_impl!(self, u64, u64::from_ne_bytes)
    }

    /// Takes an `u128` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 16`.
    #[inline]
    fn get_u128(&mut self) -> u128 {
        get_buf_impl!(self, u128, u128::from_be_bytes)
    }

    /// Takes an `u128` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 16`.
    #[inline]
    fn get_u128_le(&mut self) -> u128 {
        get_buf_impl!(self, u128, u128::from_le_bytes)
    }

    /// Takes an `u128` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 16`.
    #[inline]
    fn get_u128_ne(&mut self) -> u128 {
        get_buf_impl!(self, u128, u128::from_ne_bytes)
    }

    /// Takes an `i8` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 1`.
    #[inline]

    fn get_i8(&mut self) -> i8 {
        get_buf_impl!(self, i8, i8::from_be_bytes)
    }

    /// Takes an `i8` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 1`.
    #[inline]
    fn get_i8_le(&mut self) -> i8 {
        get_buf_impl!(self, i8, i8::from_le_bytes)
    }

    /// Takes an `i8` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 1`.
    #[inline]
    fn get_i8_ne(&mut self) -> i8 {
        get_buf_impl!(self, i8, i8::from_ne_bytes)
    }

    /// Takes an `i16` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 2`.
    #[inline]
    fn get_i16(&mut self) -> i16 {
        get_buf_impl!(self, i16, i16::from_be_bytes)
    }

    /// Takes an `i16` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 2`.
    #[inline]
    fn get_i16_le(&mut self) -> i16 {
        get_buf_impl!(self, i16, i16::from_le_bytes)
    }

    /// Takes an `i16` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 2`.
    #[inline]
    fn get_i16_ne(&mut self) -> i16 {
        get_buf_impl!(self, i16, i16::from_ne_bytes)
    }

    /// Takes an `i32` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 4`.
    #[inline]
    fn get_i32(&mut self) -> i32 {
        get_buf_impl!(self, i32, i32::from_be_bytes)
    }

    /// Takes an `i32` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 4`.
    #[inline]
    fn get_i32_le(&mut self) -> i32 {
        get_buf_impl!(self, i32, i32::from_le_bytes)
    }

    /// Takes an `i32` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 4`.
    #[inline]
    fn get_i32_ne(&mut self) -> i32 {
        get_buf_impl!(self, i32, i32::from_ne_bytes)
    }

    /// Takes an `i64` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 8`.
    #[inline]
    fn get_i64(&mut self) -> i64 {
        get_buf_impl!(self, i64, i64::from_be_bytes)
    }

    /// Takes an `i64` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 8`.
    #[inline]
    fn get_i64_le(&mut self) -> i64 {
        get_buf_impl!(self, i64, i64::from_le_bytes)
    }

    /// Takes an `i64` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 8`.
    #[inline]
    fn get_i64_ne(&mut self) -> i64 {
        get_buf_impl!(self, i64, i64::from_ne_bytes)
    }

    /// Takes an `i128` from the buffer in big-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 16`.
    #[inline]
    fn get_i128(&mut self) -> i128 {
        get_buf_impl!(self, i128, i128::from_be_bytes)
    }

    /// Takes an `i128` from the buffer in little-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 16`.
    #[inline]
    fn get_i128_le(&mut self) -> i128 {
        get_buf_impl!(self, i128, i128::from_le_bytes)
    }

    /// Takes an `i128` from the buffer in native-endian order.
    ///
    /// # Panics
    ///
    /// Panics if `self.remaining() < 16`.
    #[inline]
    fn get_i128_ne(&mut self) -> i128 {
        get_buf_impl!(self, i128, i128::from_ne_bytes)
    }

    /// Returns true if this buffer has bytes remaining.
    #[inline]
    fn has_remaining(&self) -> bool {
        self.remaining() != 0
    }

    /// Creates a [`Reader`], that implements [`Read`] and [`BufRead`].
    ///
    /// [`Read`]: std::io::Read
    /// [`BufRead`]: std::io::BufRead
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    fn reader(self) -> Reader<Self>
    where
        Self: Sized,
    {
        Reader { buf: self }
    }
}

impl Buf for &[u8] {
    #[inline]
    fn remaining(&self) -> usize {
        self.len()
    }

    #[inline]
    fn chunk(&self) -> &[u8] {
        self
    }

    #[inline]
    fn advance(&mut self, cnt: usize) {
        *self = &self[cnt..];
    }
}

impl Buf for Bytes {
    #[inline]
    fn advance(&mut self, cnt: usize) {
        if cnt > self.remaining() {
            panic!("advance {}, but remaining is {}", cnt, self.remaining());
        } else {
            // SAFETY: cnt <= self.remaining() means that ptr+cnt is still within
            // the buffer.
            unsafe {
                self.ptr = self.ptr.add(cnt);
            }
        }
    }

    #[inline]
    fn chunk(&self) -> &[u8] {
        self.as_ref()
    }

    #[inline]
    fn remaining(&self) -> usize {
        self.len()
    }

    #[inline]
    fn copy_to_bytes(&mut self, len: usize) -> Bytes {
        assert!(len <= self.remaining());

        // Shallow clone
        let mut buf = self.clone();

        // SAFETY: len <= self.remaining(), so the new buffer does not
        // overread the current buffer.
        unsafe {
            buf.set_len(len);
        }

        self.advance(len);

        buf
    }
}

impl<T> Buf for &mut T
where
    T: ?Sized + Buf,
{
    fn advance(&mut self, cnt: usize) {
        (**self).advance(cnt)
    }

    fn remaining(&self) -> usize {
        (**self).remaining()
    }

    fn chunk(&self) -> &[u8] {
        (**self).chunk()
    }
}

impl<T> Buf for alloc::boxed::Box<T>
where
    T: ?Sized + Buf,
{
    fn advance(&mut self, cnt: usize) {
        (**self).advance(cnt)
    }

    fn remaining(&self) -> usize {
        (**self).remaining()
    }

    fn chunk(&self) -> &[u8] {
        (**self).chunk()
    }
}

mod reader {
    use std::io::{self, BufRead, Read};

    use super::Buf;

    #[derive(Debug)]
    pub struct Reader<B>
    where
        B: Buf,
    {
        pub(super) buf: B,
    }

    impl<B> Reader<B>
    where
        B: Buf,
    {
        /// Returns a reference to the underlying [`Buf`].
        #[inline]
        pub fn get_ref(&self) -> &B {
            &self.buf
        }

        /// Returns a mutable reference to the underlying [`Buf`].
        #[inline]
        pub fn get_mut(&mut self) -> &mut B {
            &mut self.buf
        }

        /// Consumes the `Reader`, returning the underlying [`Buf`].
        #[inline]
        pub fn into_innter(self) -> B {
            self.buf
        }
    }

    impl<B> Read for Reader<B>
    where
        B: Buf,
    {
        #[inline]
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let len = if self.buf.remaining() < buf.len() {
                self.buf.remaining()
            } else {
                buf.len()
            };

            self.buf.copy_to_slice(&mut buf[0..len]);
            Ok(len)
        }
    }

    impl<B> BufRead for Reader<B>
    where
        B: Buf,
    {
        #[inline]
        fn fill_buf(&mut self) -> io::Result<&[u8]> {
            Ok(self.buf.chunk())
        }

        #[inline]
        fn consume(&mut self, amt: usize) {
            self.buf.advance(amt);
        }
    }
}
