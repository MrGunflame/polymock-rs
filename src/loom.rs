#[cfg(not(all(test, loom)))]
pub mod sync {
    pub mod atomic {
        pub use core::sync::atomic::{AtomicUsize, Ordering};

        pub use crate::loom::__internal::AtomicExt;

        impl AtomicExt<usize> for AtomicUsize {
            #[inline]
            fn get(&mut self) -> usize {
                *self.get_mut()
            }

            #[inline]
            fn set(&mut self, value: usize) {
                *self.get_mut() = value;
            }
        }
    }
}

#[cfg(all(test, loom))]
pub mod sync {
    pub mod atomic {
        pub use loom::sync::atomic::{AtomicUsize, Ordering};

        pub use crate::loom::__internal::AtomicExt;

        impl AtomicExt<usize> for AtomicUsize {
            #[inline]
            fn get(&mut self) -> usize {
                self.with_mut(|val| *val)
            }

            fn set(&mut self, value: usize) {
                self.with_mut(|cell| {
                    *cell = value;
                });
            }
        }
    }
}

mod __internal {
    pub trait AtomicExt<T> {
        fn get(&mut self) -> T;

        fn set(&mut self, value: T);
    }
}
