#[cfg(not(all(test, loom)))]
pub mod sync {
    pub mod atomic {
        pub use core::sync::atomic::{AtomicUsize, Ordering};
    }
}

#[cfg(all(test, loom))]
pub mod sync {
    pub mod atomic {
        pub use loom::sync::atomic::{AtomicUsize, Ordering};
    }
}
