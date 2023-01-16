#[derive(Clone, Debug)]
pub struct Arena {}

struct Chunk {}

#[derive(Debug)]
pub struct BytesMut {
    ptr: *mut u8,
    len: usize,
}
