#![no_std]

mod bump;
mod ring;

use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;

pub use bump::Mark;
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

    pub fn mark(&self) -> Mark {
        unsafe { (*self.inner.get()).mark() }
    }

    /// # Safety
    /// All allocations made after the mark must not be used after this call.
    pub unsafe fn reset(&self, mark: Mark) {
        unsafe { (*self.inner.get()).reset(mark) }
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
    fn public_api_mark_reset() {
        with_allocator(|alloc| {
            let layout = Layout::from_size_align(64, 8).unwrap();
            let mark = alloc.mark();
            unsafe {
                let p1 = alloc.alloc(layout);
                assert!(!p1.is_null());
                let p2 = alloc.alloc(layout);
                assert!(!p2.is_null());
                alloc.reset(mark);
                // can re-use space
                let p3 = alloc.alloc(layout);
                assert!(!p3.is_null());
                assert_eq!(p3, p1);
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
