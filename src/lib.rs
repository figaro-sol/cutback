#![no_std]

mod bump;
mod ring;
mod tracker;

#[cfg(test)]
mod proptest_tests;

#[cfg(any(test, fuzzing))]
pub mod test_harness;

use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;

#[cfg(not(any(test, fuzzing)))]
use bump::MarkNode;
#[cfg(any(test, fuzzing))]
pub use bump::MarkNode;

use bump::ScopedBumpInner;

/// Single-threaded scoped bump allocator.
///
/// `unsafe impl Sync` exists solely to allow use as a `#[global_allocator]` static.
/// Concurrent access from multiple threads is undefined behavior.
pub struct ScopedBump<const N: usize> {
    inner: UnsafeCell<ScopedBumpInner<N>>,
}

// SAFETY: Only sound for single-threaded use (e.g. #[global_allocator] statics).
// Concurrent access is UB — the inner UnsafeCell has no synchronization.
unsafe impl<const N: usize> Sync for ScopedBump<N> {}

impl<const N: usize> ScopedBump<N> {
    pub const fn new_uninit() -> Self {
        Self {
            inner: UnsafeCell::new(ScopedBumpInner::new_uninit()),
        }
    }

    /// # Safety
    /// Must be called exactly once before any allocation. `base` must point to
    /// a valid region of at least `cap` bytes that outlives all allocations.
    pub unsafe fn init(&self, base: *mut u8, cap: usize) {
        unsafe { (*self.inner.get()).init(base, cap) }
    }

    #[cfg(any(test, fuzzing))]
    pub unsafe fn push_mark(&self, node: &mut MarkNode<N>) {
        (*self.inner.get()).push_mark(node);
    }

    #[cfg(any(test, fuzzing))]
    pub unsafe fn pop_mark_and_reset(&self) {
        (*self.inner.get()).pop_mark_and_reset();
    }

    /// # Safety
    /// Allocations made during `f` are invalidated when `with_mark` returns.
    /// Caller must not use those pointers afterward.
    pub unsafe fn with_mark<R>(&self, f: impl FnOnce() -> R) -> R {
        let mut node = MarkNode::<N>::uninit();
        (*self.inner.get()).push_mark(&mut node);
        struct Guard<'a, const M: usize>(&'a ScopedBump<M>);
        impl<const M: usize> Drop for Guard<'_, M> {
            fn drop(&mut self) {
                unsafe { (*self.0.inner.get()).pop_mark_and_reset() };
            }
        }
        let guard = Guard(self);
        let result = f();
        drop(guard);
        result
    }
}

unsafe impl<const N: usize> GlobalAlloc for ScopedBump<N> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { (*self.inner.get()).alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { (*self.inner.get()).dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        unsafe { (*self.inner.get()).realloc(ptr, layout, new_size) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::alloc::Layout;

    fn with_allocator<F: FnOnce(&ScopedBump<8>)>(f: F) {
        let mut arena = [0u8; 4096];
        let alloc = ScopedBump::<8>::new_uninit();
        unsafe { alloc.init(arena.as_mut_ptr(), arena.len()) };
        f(&alloc);
    }

    #[test]
    fn public_api_alloc_dealloc() {
        with_allocator(|alloc| {
            let layout = Layout::from_size_align(64, 8).unwrap();
            unsafe {
                let ptr = alloc.alloc(layout);
                assert!(!ptr.is_null());
                assert_eq!((ptr as usize) % 8, 0);
                alloc.dealloc(ptr, layout);
            }
        });
    }

    #[test]
    fn public_api_with_mark() {
        with_allocator(|alloc| {
            let layout = Layout::from_size_align(64, 8).unwrap();
            unsafe {
                alloc.with_mark(|| {
                    let p1 = alloc.alloc(layout);
                    assert!(!p1.is_null());
                    let p2 = alloc.alloc(layout);
                    assert!(!p2.is_null());
                });
                // space reclaimed — can re-use from the beginning
                let p3 = alloc.alloc(layout);
                assert!(!p3.is_null());
            }
        });
    }

    #[test]
    fn public_api_realloc() {
        with_allocator(|alloc| {
            let layout = Layout::from_size_align(16, 4).unwrap();
            unsafe {
                let ptr = alloc.alloc(layout);
                assert!(!ptr.is_null());
                core::ptr::write_bytes(ptr, 0xDD, 16);
                let new_ptr = alloc.realloc(ptr, layout, 64);
                assert!(!new_ptr.is_null());
                // data preserved
                for i in 0..16 {
                    assert_eq!(*new_ptr.add(i), 0xDD);
                }
            }
        });
    }

    #[test]
    fn const_new_uninit() {
        // Verify it works in a const/static context
        static _ALLOC: ScopedBump<32> = ScopedBump::new_uninit();
    }
}
