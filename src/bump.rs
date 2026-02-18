use core::alloc::Layout;
use core::ptr;
use core::ptr::NonNull;

use crate::ring::{RecentAlloc, RingBuffer};

#[cfg(fuzzing)]
extern crate alloc;

#[cfg(fuzzing)]
struct AllocInfo {
    size: usize,
    align: usize,
}

pub struct MarkNode {
    cursor: usize,
    prev: Option<NonNull<MarkNode>>,
}

impl MarkNode {
    pub const fn uninit() -> Self {
        Self {
            cursor: 0,
            prev: None,
        }
    }
}

enum MarkState {
    Unmarked,
    Marked { head: NonNull<MarkNode> },
}

pub(crate) struct ScopedBumpInner<const N: usize> {
    base: *mut u8,
    cap: usize,
    cursor: usize,
    ring: RingBuffer<N>,
    mark_state: MarkState,
    #[cfg(fuzzing)]
    tracker: alloc::collections::BTreeMap<usize, AllocInfo>,
}

impl<const N: usize> ScopedBumpInner<N> {
    pub const fn new_uninit() -> Self {
        Self {
            base: core::ptr::null_mut(),
            cap: 0,
            cursor: 0,
            ring: RingBuffer::new(),
            mark_state: MarkState::Unmarked,
            #[cfg(fuzzing)]
            tracker: alloc::collections::BTreeMap::new(),
        }
    }

    pub unsafe fn init(&mut self, base: *mut u8, cap: usize) {
        assert!(self.base.is_null(), "init called twice");
        self.base = base;
        self.cap = cap;
    }

    fn is_marked(&self) -> bool {
        matches!(self.mark_state, MarkState::Marked { .. })
    }

    pub fn alloc(&mut self, layout: Layout) -> *mut u8 {
        if layout.size() == 0 {
            return ptr::without_provenance_mut(layout.align());
        }
        let abs_addr = (self.base as usize) + self.cursor;
        let aligned_addr = match align_up(abs_addr, layout.align()) {
            Some(v) => v,
            None => return ptr::null_mut(),
        };
        let aligned = aligned_addr - self.base as usize;
        let end = match aligned.checked_add(layout.size()) {
            Some(v) if v <= self.cap => v,
            _ => return ptr::null_mut(),
        };
        if !self.is_marked() {
            self.ring.push(RecentAlloc {
                offset: aligned,
                size: layout.size(),
                alive: true,
            });
        }
        self.cursor = end;
        #[cfg(fuzzing)]
        {
            if let Some((&off, info)) = self.tracker.range(..=aligned).next_back() {
                debug_assert!(
                    off + info.size <= aligned,
                    "alloc overlap: existing [{off}..{}) overlaps new [{aligned}..{})",
                    off + info.size,
                    aligned + layout.size()
                );
            }
            if let Some((&off, _)) = self.tracker.range(aligned..).next() {
                debug_assert!(
                    aligned + layout.size() <= off,
                    "alloc overlap: new [{aligned}..{}) overlaps existing [{off}..)",
                    aligned + layout.size()
                );
            }
            self.tracker.insert(
                aligned,
                AllocInfo {
                    size: layout.size(),
                    align: layout.align(),
                },
            );
        }
        unsafe { self.base.add(aligned) }
    }

    pub unsafe fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        if layout.size() == 0 {
            return;
        }
        if (ptr as usize) < (self.base as usize)
            || (ptr as usize) >= (self.base as usize) + self.cap
        {
            return;
        }
        let offset = ptr as usize - self.base as usize;
        #[cfg(fuzzing)]
        {
            match self.tracker.remove(&offset) {
                Some(info) => {
                    debug_assert_eq!(
                        layout.size(),
                        info.size,
                        "dealloc size mismatch at offset {offset}: got {}, stored {}",
                        layout.size(),
                        info.size
                    );
                    debug_assert_eq!(
                        layout.align(),
                        info.align,
                        "dealloc align mismatch at offset {offset}"
                    );
                }
                None => debug_assert!(
                    false,
                    "dealloc of untracked offset {offset} (double-free or invalid)"
                ),
            }
        }
        let idx = match self.ring.find_by_offset(offset) {
            Some(i) => i,
            None => return,
        };
        self.ring.mark_dead(idx);
        if !self.is_marked() {
            if let Some(rewind_to) = self.ring.suffix_rewind_cursor() {
                self.cursor = rewind_to;
            }
        }
    }

    pub unsafe fn realloc(&mut self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if layout.size() == 0 {
            let new_layout = match Layout::from_size_align(new_size, layout.align()) {
                Ok(l) => l,
                Err(_) => return ptr::null_mut(),
            };
            return self.alloc(new_layout);
        }
        if new_size == 0 {
            self.dealloc(ptr, layout);
            return ptr::without_provenance_mut(layout.align());
        }
        if (ptr as usize) < (self.base as usize)
            || (ptr as usize) >= (self.base as usize) + self.cap
        {
            return ptr::null_mut();
        }
        let offset = ptr as usize - self.base as usize;
        // Case A: newest alive allocation — try in-place (only when unmarked;
        // ring is frozen during marks so newest() would be a stale pre-mark entry)
        if !self.is_marked() {
            if let Some(newest) = self.ring.newest() {
                if newest.alive && newest.offset == offset {
                    let new_end = match offset.checked_add(new_size) {
                        Some(v) if v <= self.cap => v,
                        _ => return ptr::null_mut(),
                    };
                    self.cursor = new_end;
                    self.ring.update_newest_size(new_size);
                    #[cfg(fuzzing)]
                    if let Some(info) = self.tracker.get_mut(&offset) {
                        debug_assert_eq!(layout.size(), info.size);
                        debug_assert_eq!(layout.align(), info.align);
                        info.size = new_size;
                    } else {
                        debug_assert!(false, "in-place realloc of untracked offset {offset}");
                    }
                    return ptr;
                }
            }
        }
        // Case B: not newest — alloc new, copy, dealloc old
        let new_layout = match Layout::from_size_align(new_size, layout.align()) {
            Ok(l) => l,
            Err(_) => return ptr::null_mut(),
        };
        let new_ptr = self.alloc(new_layout);
        if new_ptr.is_null() {
            return ptr::null_mut();
        }
        let copy_size = layout.size().min(new_size);
        ptr::copy_nonoverlapping(ptr, new_ptr, copy_size);
        self.dealloc(ptr, layout);
        new_ptr
    }

    pub fn push_mark(&mut self, node: &mut MarkNode) {
        node.cursor = self.cursor;
        node.prev = match self.mark_state {
            MarkState::Marked { head } => Some(head),
            MarkState::Unmarked => None,
        };
        self.mark_state = MarkState::Marked {
            head: NonNull::from(&mut *node),
        };
    }

    pub fn pop_mark_and_reset(&mut self) {
        let head = match self.mark_state {
            MarkState::Marked { head } => head,
            MarkState::Unmarked => panic!("no active mark to pop"),
        };
        let node = unsafe { head.as_ref() };
        let saved = node.cursor;
        self.mark_state = match node.prev {
            Some(prev) => MarkState::Marked { head: prev },
            None => MarkState::Unmarked,
        };
        if saved < self.cursor {
            self.cursor = saved;
            self.ring.invalidate_from_offset(saved);
            #[cfg(fuzzing)]
            {
                let to_remove: alloc::vec::Vec<usize> =
                    self.tracker.range(saved..).map(|(&k, _)| k).collect();
                for off in to_remove {
                    self.tracker.remove(&off);
                }
            }
        }
        // On transition to Unmarked, recover space from pre-mark frees
        // NOTE: For deep/long-lived nested marks needing full ring semantics,
        // a per-mark ring snapshot approach could restore the ring to its exact
        // state at mark time. Current approach (freeze ring during marks) is
        // simpler and sufficient for typical short-lived tactical mark usage.
        if !self.is_marked() {
            if let Some(rewind_to) = self.ring.suffix_rewind_cursor() {
                self.cursor = rewind_to;
            }
        }
    }
}

pub(crate) fn align_up(offset: usize, align: usize) -> Option<usize> {
    debug_assert!(align.is_power_of_two());
    let mask = align - 1;
    offset.checked_add(mask).map(|v| v & !mask)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_bump<const N: usize>(arena: &mut [u8]) -> ScopedBumpInner<N> {
        let mut bump = ScopedBumpInner::<N>::new_uninit();
        unsafe { bump.init(arena.as_mut_ptr(), arena.len()) };
        bump
    }

    #[test]
    fn single_alloc() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let layout = Layout::from_size_align(16, 4).unwrap();
        let ptr = bump.alloc(layout);
        assert!(!ptr.is_null());
        let base = arena.as_ptr();
        assert!(ptr as usize >= base as usize);
        assert!(ptr as usize + 16 <= base as usize + 1024);
        assert_eq!((ptr as usize) % 4, 0);
    }

    #[test]
    fn sequential_allocs_dont_overlap() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l1 = Layout::from_size_align(16, 4).unwrap();
        let l2 = Layout::from_size_align(32, 8).unwrap();
        let p1 = bump.alloc(l1);
        let p2 = bump.alloc(l2);
        assert!(!p1.is_null());
        assert!(!p2.is_null());
        // p2 starts at or after p1+16
        assert!(p2 as usize >= p1 as usize + 16);
        assert_eq!((p2 as usize) % 8, 0);
    }

    #[test]
    fn alignment_gaps() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        // alloc 1 byte with align 1
        let l1 = Layout::from_size_align(1, 1).unwrap();
        let p1 = bump.alloc(l1);
        assert!(!p1.is_null());
        // alloc with align 8 — should skip bytes
        let l2 = Layout::from_size_align(8, 8).unwrap();
        let p2 = bump.alloc(l2);
        assert!(!p2.is_null());
        assert_eq!((p2 as usize) % 8, 0);
        assert!(p2 as usize > p1 as usize);
    }

    #[test]
    fn oom_returns_null() {
        let mut arena = [0u8; 16];
        let mut bump = make_bump::<8>(&mut arena);
        let layout = Layout::from_size_align(32, 1).unwrap();
        let ptr = bump.alloc(layout);
        assert!(ptr.is_null());
    }

    #[test]
    fn oom_after_partial_fill() {
        let mut arena = [0u8; 32];
        let mut bump = make_bump::<8>(&mut arena);
        let l1 = Layout::from_size_align(24, 1).unwrap();
        let p1 = bump.alloc(l1);
        assert!(!p1.is_null());
        let l2 = Layout::from_size_align(16, 1).unwrap();
        let p2 = bump.alloc(l2);
        assert!(p2.is_null());
    }

    #[test]
    fn dealloc_single_rewinds() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let layout = Layout::from_size_align(16, 1).unwrap();
        let ptr = bump.alloc(layout);
        assert_eq!(bump.cursor, 16);
        unsafe { bump.dealloc(ptr, layout) };
        assert_eq!(bump.cursor, 0);
    }

    #[test]
    fn dealloc_lifo_full_rewind() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l);
        let b = bump.alloc(l);
        let c = bump.alloc(l);
        assert_eq!(bump.cursor, 48);
        unsafe { bump.dealloc(c, l) };
        assert_eq!(bump.cursor, 32);
        unsafe { bump.dealloc(b, l) };
        assert_eq!(bump.cursor, 16);
        unsafe { bump.dealloc(a, l) };
        assert_eq!(bump.cursor, 0);
    }

    #[test]
    fn dealloc_middle_no_rewind() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l);
        let _b = bump.alloc(l);
        let _c = bump.alloc(l);
        assert_eq!(bump.cursor, 48);
        unsafe { bump.dealloc(a, l) };
        assert_eq!(bump.cursor, 48);
    }

    #[test]
    fn dealloc_out_of_order_then_rewind() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let _a = bump.alloc(l);
        let b = bump.alloc(l);
        let c = bump.alloc(l);
        // dealloc C then B: after C, cursor rewinds to 32; after B, to 16
        unsafe { bump.dealloc(c, l) };
        assert_eq!(bump.cursor, 32);
        unsafe { bump.dealloc(b, l) };
        assert_eq!(bump.cursor, 16);
    }

    #[test]
    fn dealloc_evicted_ptr_is_noop() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<2>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l);
        let _b = bump.alloc(l);
        let _c = bump.alloc(l); // evicts a from ring
        let cursor_before = bump.cursor;
        unsafe { bump.dealloc(a, l) };
        assert_eq!(bump.cursor, cursor_before);
    }

    #[test]
    fn double_dealloc_is_noop() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l);
        unsafe { bump.dealloc(a, l) };
        assert_eq!(bump.cursor, 0);
        // second dealloc: already dead, find_by_offset returns None
        unsafe { bump.dealloc(a, l) };
        assert_eq!(bump.cursor, 0);
    }

    #[test]
    fn realloc_in_place_grow() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let ptr = bump.alloc(l);
        unsafe { ptr::write_bytes(ptr, 0xAA, 16) };
        let new_ptr = unsafe { bump.realloc(ptr, l, 32) };
        assert_eq!(new_ptr, ptr);
        assert_eq!(bump.cursor, 32);
        // old data preserved
        for i in 0..16 {
            assert_eq!(unsafe { *new_ptr.add(i) }, 0xAA);
        }
    }

    #[test]
    fn realloc_in_place_shrink() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(32, 1).unwrap();
        let ptr = bump.alloc(l);
        let new_ptr = unsafe { bump.realloc(ptr, l, 8) };
        assert_eq!(new_ptr, ptr);
        assert_eq!(bump.cursor, 8);
    }

    #[test]
    fn realloc_fallback_not_newest() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l);
        unsafe { ptr::write_bytes(a, 0xBB, 16) };
        let _b = bump.alloc(l);
        // realloc a (not newest) -> fallback
        let new_a = unsafe { bump.realloc(a, l, 32) };
        assert!(!new_a.is_null());
        assert_ne!(new_a, a);
        // old data preserved in min(16, 32) = 16 bytes
        for i in 0..16 {
            assert_eq!(unsafe { *new_a.add(i) }, 0xBB);
        }
    }

    #[test]
    fn realloc_grow_past_cap() {
        let mut arena = [0u8; 64];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(32, 1).unwrap();
        let ptr = bump.alloc(l);
        assert!(!ptr.is_null());
        let new_ptr = unsafe { bump.realloc(ptr, l, 128) };
        assert!(new_ptr.is_null());
    }

    #[test]
    fn realloc_after_dealloc_of_newest_uses_fallback() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l);
        let b = bump.alloc(l);
        unsafe { ptr::write_bytes(a, 0xCC, 16) };
        // dealloc b (newest), so newest in ring is now dead
        unsafe { bump.dealloc(b, l) };
        // realloc a: newest is dead, so alive check fails -> fallback
        let new_a = unsafe { bump.realloc(a, l, 32) };
        assert!(!new_a.is_null());
        for i in 0..16 {
            assert_eq!(unsafe { *new_a.add(i) }, 0xCC);
        }
    }

    #[test]
    fn mark_reset_basic() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let _a = bump.alloc(l);
        let mut mark = MarkNode::uninit();
        bump.push_mark(&mut mark);
        let _b = bump.alloc(l);
        let _c = bump.alloc(l);
        assert_eq!(bump.cursor, 48);
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 16);
    }

    #[test]
    fn mark_reset_already_rewound() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let _a = bump.alloc(l);
        let mut mark = MarkNode::uninit();
        bump.push_mark(&mut mark);
        let b = bump.alloc(l);
        // dealloc b: ring is frozen so b isn't tracked — dealloc is a no-op
        unsafe { bump.dealloc(b, l) };
        assert_eq!(bump.cursor, 32);
        // pop rewinds cursor to mark's saved cursor (16)
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 16);
    }

    #[test]
    fn nested_marks() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let mut mark_outer = MarkNode::uninit();
        bump.push_mark(&mut mark_outer);
        let _a = bump.alloc(l);
        let mut mark_inner = MarkNode::uninit();
        bump.push_mark(&mut mark_inner);
        let _b = bump.alloc(l);
        assert_eq!(bump.cursor, 32);
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 16);
        // alloc again after inner reset
        let _c = bump.alloc(l);
        assert_eq!(bump.cursor, 32);
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 0);
    }

    #[test]
    fn reset_to_zero_invalidates_all() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let mut mark = MarkNode::uninit();
        bump.push_mark(&mut mark);
        let l = Layout::from_size_align(16, 1).unwrap();
        let _a = bump.alloc(l);
        let _b = bump.alloc(l);
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 0);
        // can alloc from beginning again
        let c = bump.alloc(l);
        assert!(!c.is_null());
        assert_eq!(bump.cursor, 16);
    }

    #[test]
    #[should_panic(expected = "no active mark to pop")]
    fn pop_mark_empty_panics() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        bump.pop_mark_and_reset();
    }

    #[test]
    fn nested_push_pop() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let _a = bump.alloc(l);
        assert_eq!(bump.cursor, 16);
        let mut mark_outer = MarkNode::uninit();
        bump.push_mark(&mut mark_outer);
        let _b = bump.alloc(l);
        assert_eq!(bump.cursor, 32);
        let mut mark_inner = MarkNode::uninit();
        bump.push_mark(&mut mark_inner);
        let _c = bump.alloc(l);
        assert_eq!(bump.cursor, 48);
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 32);
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 16);
    }

    #[test]
    fn realloc_grow_blocked_across_mark() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l);
        assert!(!a.is_null());
        unsafe { ptr::write_bytes(a, 0xAA, 16) };
        let mut mark = MarkNode::uninit();
        bump.push_mark(&mut mark);
        // realloc A larger — ring frozen during mark, must fall back
        let new_a = unsafe { bump.realloc(a, l, 32) };
        assert!(!new_a.is_null());
        assert_ne!(new_a, a, "should not be in-place during mark");
        for i in 0..16 {
            assert_eq!(unsafe { *new_a.add(i) }, 0xAA);
        }
        bump.pop_mark_and_reset();
    }

    #[test]
    fn realloc_grow_within_scope() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let mut mark = MarkNode::uninit();
        bump.push_mark(&mut mark);
        let l = Layout::from_size_align(16, 1).unwrap();
        let b = bump.alloc(l);
        assert!(!b.is_null());
        unsafe { ptr::write_bytes(b, 0xAA, 16) };
        // realloc B larger — ring frozen, in-place skipped, uses fallback
        let new_b = unsafe { bump.realloc(b, l, 32) };
        assert!(!new_b.is_null());
        assert_ne!(new_b, b, "should fall back when ring is frozen");
        for i in 0..16 {
            assert_eq!(unsafe { *new_b.add(i) }, 0xAA);
        }
        bump.pop_mark_and_reset();
    }

    #[test]
    fn realloc_shrink_across_mark_ok() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(32, 1).unwrap();
        let a = bump.alloc(l);
        assert!(!a.is_null());
        unsafe { ptr::write_bytes(a, 0xBB, 32) };
        let mut mark = MarkNode::uninit();
        bump.push_mark(&mut mark);
        // shrink A — ring frozen, in-place skipped, uses fallback
        let new_a = unsafe { bump.realloc(a, l, 8) };
        assert!(!new_a.is_null());
        assert_ne!(new_a, a, "should fall back when ring is frozen");
        for i in 0..8 {
            assert_eq!(unsafe { *new_a.add(i) }, 0xBB);
        }
        bump.pop_mark_and_reset();
        // pop rewinds to mark cursor (32), then suffix_rewind recovers
        // the dead pre-mark alloc (a at offset 0), cursor goes to 0
        assert_eq!(bump.cursor, 0);
    }

    #[test]
    fn align_up_already_aligned() {
        assert_eq!(align_up(0, 1), Some(0));
        assert_eq!(align_up(0, 8), Some(0));
        assert_eq!(align_up(8, 8), Some(8));
        assert_eq!(align_up(16, 4), Some(16));
    }

    #[test]
    fn align_up_needs_padding() {
        assert_eq!(align_up(1, 4), Some(4));
        assert_eq!(align_up(5, 8), Some(8));
        assert_eq!(align_up(9, 4), Some(12));
        assert_eq!(align_up(7, 8), Some(8));
    }

    #[test]
    fn align_up_overflow() {
        assert_eq!(align_up(usize::MAX, 8), None);
        assert_eq!(align_up(usize::MAX - 1, 8), None);
        assert_eq!(align_up(usize::MAX - 6, 8), None);
    }

    #[test]
    fn align_up_align_1() {
        assert_eq!(align_up(0, 1), Some(0));
        assert_eq!(align_up(1, 1), Some(1));
        assert_eq!(align_up(usize::MAX, 1), Some(usize::MAX));
    }

    #[test]
    fn zst_alloc_returns_aligned_non_null() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let layout = Layout::from_size_align(0, 4).unwrap();
        let ptr = bump.alloc(layout);
        assert!(!ptr.is_null());
        assert_eq!((ptr as usize) % 4, 0);
    }

    #[test]
    fn zst_alloc_does_not_advance_cursor() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let zst = Layout::from_size_align(0, 1).unwrap();
        let cursor_before = bump.cursor;
        let _ = bump.alloc(zst);
        let _ = bump.alloc(zst);
        let _ = bump.alloc(zst);
        assert_eq!(bump.cursor, cursor_before);
    }

    #[test]
    fn zst_dealloc_is_noop() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let zst = Layout::from_size_align(0, 4).unwrap();
        let ptr = bump.alloc(zst);
        let cursor_before = bump.cursor;
        unsafe { bump.dealloc(ptr, zst) };
        assert_eq!(bump.cursor, cursor_before);
    }

    #[test]
    fn realloc_from_zst_to_sized() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let zst = Layout::from_size_align(0, 4).unwrap();
        let ptr = bump.alloc(zst);
        let cursor_before = bump.cursor;
        let new_ptr = unsafe { bump.realloc(ptr, zst, 32) };
        assert!(!new_ptr.is_null());
        assert_eq!((new_ptr as usize) % 4, 0);
        assert!(bump.cursor > cursor_before);
    }

    #[test]
    fn realloc_from_sized_to_zst() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let layout = Layout::from_size_align(16, 4).unwrap();
        let ptr = bump.alloc(layout);
        assert!(!ptr.is_null());
        let alloc_offset = ptr as usize - arena.as_ptr() as usize;
        let new_ptr = unsafe { bump.realloc(ptr, layout, 0) };
        assert!(!new_ptr.is_null());
        assert_eq!((new_ptr as usize) % 4, 0);
        // cursor should have rewound to the start of the deallocated allocation
        assert!(bump.cursor <= alloc_offset);
    }

    #[test]
    fn alloc_alignment_with_misaligned_base() {
        let mut arena = [0u8; 1025];
        let base = arena.as_mut_ptr();
        // Ensure base is NOT 8-byte aligned
        let offset = if (base as usize).is_multiple_of(8) {
            1
        } else {
            0
        };
        let misaligned_base = unsafe { base.add(offset) };
        assert_ne!((misaligned_base as usize) % 8, 0);

        let mut bump = ScopedBumpInner::<8>::new_uninit();
        unsafe { bump.init(misaligned_base, 1024) };

        let layout = Layout::from_size_align(16, 8).unwrap();
        let ptr = bump.alloc(layout);
        assert!(!ptr.is_null());
        assert_eq!(
            (ptr as usize) % 8,
            0,
            "alloc returned misaligned pointer: {:p} (base={:p})",
            ptr,
            misaligned_base
        );
    }

    #[test]
    fn sequential_allocs_aligned_with_misaligned_base() {
        let mut arena = [0u8; 2049];
        let base = arena.as_mut_ptr();
        let offset = if (base as usize).is_multiple_of(16) {
            1
        } else {
            0
        };
        let misaligned_base = unsafe { base.add(offset) };

        let mut bump = ScopedBumpInner::<8>::new_uninit();
        unsafe { bump.init(misaligned_base, 2048) };

        let l1 = Layout::from_size_align(7, 1).unwrap();
        let l2 = Layout::from_size_align(16, 16).unwrap();
        let l3 = Layout::from_size_align(8, 8).unwrap();

        let p1 = bump.alloc(l1);
        assert!(!p1.is_null());
        assert_eq!((p1 as usize) % l1.align(), 0);

        let p2 = bump.alloc(l2);
        assert!(!p2.is_null());
        assert_eq!(
            (p2 as usize) % 16,
            0,
            "16-byte aligned alloc returned misaligned pointer: {:p}",
            p2
        );

        let p3 = bump.alloc(l3);
        assert!(!p3.is_null());
        assert_eq!((p3 as usize) % 8, 0);

        // no overlap
        assert!(p2 as usize >= p1 as usize + 7);
        assert!(p3 as usize >= p2 as usize + 16);
    }

    #[test]
    fn ring_clean_after_mark_scope() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l);
        assert_eq!(bump.cursor, 16);
        let mut mark = MarkNode::uninit();
        bump.push_mark(&mut mark);
        // alloc and dealloc inside mark — ring stays frozen
        let b = bump.alloc(l);
        let _c = bump.alloc(l);
        unsafe { bump.dealloc(b, l) };
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 16);
        // pre-mark LIFO still works: dealloc a rewinds to 0
        unsafe { bump.dealloc(a, l) };
        assert_eq!(bump.cursor, 0);
    }

    #[test]
    fn pre_mark_frees_recovered_on_pop() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l);
        let b = bump.alloc(l);
        assert_eq!(bump.cursor, 32);
        let mut mark = MarkNode::uninit();
        bump.push_mark(&mut mark);
        // dealloc pre-mark allocs during mark — marks them dead but no rewind
        unsafe { bump.dealloc(b, l) };
        unsafe { bump.dealloc(a, l) };
        assert_eq!(bump.cursor, 32);
        // pop transitions to Unmarked, suffix_rewind recovers space
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 0);
    }

    #[test]
    fn ring_eviction_before_mark_space_leaked() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<2>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l); // offset 0, ring=[A]
        let b = bump.alloc(l); // offset 16, ring=[A,B]
        let c = bump.alloc(l); // offset 32, ring=[B,C], A evicted
        assert_eq!(bump.cursor, 48);
        let mut mark = MarkNode::uninit();
        bump.push_mark(&mut mark); // saved=48, ring frozen
        unsafe { bump.dealloc(a, l) }; // no-op: A evicted from ring
        assert_eq!(bump.cursor, 48);
        unsafe { bump.dealloc(b, l) }; // mark_dead but no rewind (marked)
        unsafe { bump.dealloc(c, l) }; // mark_dead but no rewind (marked)
        assert_eq!(bump.cursor, 48);
        bump.pop_mark_and_reset();
        // B and C (both dead) are suffix-rewound: cursor → 16
        // A's space [0..16) is permanently leaked (evicted, never recovered)
        assert_eq!(bump.cursor, 16);
    }

    #[test]
    fn ring_eviction_lifo_still_works_for_tracked() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<2>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l); // offset 0, ring=[A]
        let b = bump.alloc(l); // offset 16, ring=[A,B]
        let c = bump.alloc(l); // offset 32, ring=[B,C], A evicted
        assert_eq!(bump.cursor, 48);
        // LIFO dealloc of ring-tracked entries recovers space
        unsafe { bump.dealloc(c, l) };
        assert_eq!(bump.cursor, 32);
        unsafe { bump.dealloc(b, l) };
        assert_eq!(bump.cursor, 16);
        // A was evicted — dealloc is a no-op, cursor unchanged
        unsafe { bump.dealloc(a, l) };
        assert_eq!(bump.cursor, 16);
    }

    #[test]
    fn nested_marks_recover_only_on_outermost_pop() {
        let mut arena = [0u8; 1024];
        let mut bump = make_bump::<8>(&mut arena);
        let l = Layout::from_size_align(16, 1).unwrap();
        let a = bump.alloc(l);
        let b = bump.alloc(l);
        assert_eq!(bump.cursor, 32);
        let mut mark_outer = MarkNode::uninit();
        bump.push_mark(&mut mark_outer);
        let mut mark_inner = MarkNode::uninit();
        bump.push_mark(&mut mark_inner);
        // dealloc pre-mark allocs inside inner mark
        unsafe { bump.dealloc(b, l) };
        unsafe { bump.dealloc(a, l) };
        assert_eq!(bump.cursor, 32);
        // inner pop: still marked (outer), no suffix_rewind
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 32);
        // outer pop: transitions to Unmarked, suffix_rewind recovers
        bump.pop_mark_and_reset();
        assert_eq!(bump.cursor, 0);
    }
}
