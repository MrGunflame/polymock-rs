use polymock::Arena;

#[test]
fn test_basic() {
    let arena = Arena::default();

    let mut buf = arena.alloc(1500);

    for (i, b) in buf.as_mut().iter_mut().enumerate() {
        *b = i as u8;
    }

    let buf = buf.freeze();

    for (i, b) in buf.as_ref().iter().enumerate() {
        assert_eq!(*b, i as u8);
    }

    let buf2 = buf.clone();
    for (i, b) in buf2.as_ref().iter().enumerate() {
        assert_eq!(*b, i as u8);
    }

    drop(buf);
    for (i, b) in buf2.as_ref().iter().enumerate() {
        assert_eq!(*b, i as u8);
    }
}
