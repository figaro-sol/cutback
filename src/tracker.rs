#[cfg(fuzzing)]
extern crate alloc;

#[cfg(fuzzing)]
struct AllocInfo {
    size: usize,
    align: usize,
}

#[cfg(fuzzing)]
pub(crate) struct AllocTracker {
    map: alloc::collections::BTreeMap<usize, AllocInfo>,
}

#[cfg(fuzzing)]
impl AllocTracker {
    pub const fn new() -> Self {
        Self {
            map: alloc::collections::BTreeMap::new(),
        }
    }

    pub fn on_alloc(&mut self, offset: usize, size: usize, align: usize) {
        if let Some((&off, info)) = self.map.range(..=offset).next_back() {
            debug_assert!(
                off + info.size <= offset,
                "alloc overlap: existing [{off}..{}) overlaps new [{offset}..{})",
                off + info.size,
                offset + size
            );
        }
        if let Some((&off, _)) = self.map.range(offset..).next() {
            debug_assert!(
                offset + size <= off,
                "alloc overlap: new [{offset}..{}) overlaps existing [{off}..)",
                offset + size
            );
        }
        self.map.insert(offset, AllocInfo { size, align });
    }

    pub fn on_dealloc(&mut self, offset: usize, size: usize, align: usize) {
        match self.map.remove(&offset) {
            Some(info) => {
                debug_assert_eq!(
                    size, info.size,
                    "dealloc size mismatch at offset {offset}: got {size}, stored {}",
                    info.size
                );
                debug_assert_eq!(
                    align, info.align,
                    "dealloc align mismatch at offset {offset}"
                );
            }
            None => debug_assert!(
                false,
                "dealloc of untracked offset {offset} (double-free or invalid)"
            ),
        }
    }

    pub fn on_realloc_in_place(
        &mut self,
        offset: usize,
        old_size: usize,
        align: usize,
        new_size: usize,
    ) {
        if let Some(info) = self.map.get_mut(&offset) {
            debug_assert_eq!(old_size, info.size);
            debug_assert_eq!(align, info.align);
            info.size = new_size;
        } else {
            debug_assert!(false, "in-place realloc of untracked offset {offset}");
        }
    }

    pub fn on_mark_reset(&mut self, saved_cursor: usize) {
        let to_remove: alloc::vec::Vec<usize> =
            self.map.range(saved_cursor..).map(|(&k, _)| k).collect();
        for off in to_remove {
            self.map.remove(&off);
        }
    }
}

#[cfg(not(fuzzing))]
pub(crate) struct NoopTracker;

#[cfg(not(fuzzing))]
impl NoopTracker {
    pub const fn new() -> Self {
        NoopTracker
    }

    #[inline(always)]
    pub fn on_alloc(&mut self, _offset: usize, _size: usize, _align: usize) {}

    #[inline(always)]
    pub fn on_dealloc(&mut self, _offset: usize, _size: usize, _align: usize) {}

    #[inline(always)]
    pub fn on_realloc_in_place(
        &mut self,
        _offset: usize,
        _old_size: usize,
        _align: usize,
        _new_size: usize,
    ) {
    }

    #[inline(always)]
    pub fn on_mark_reset(&mut self, _saved_cursor: usize) {}
}

#[cfg(fuzzing)]
pub(crate) type ActiveTracker = AllocTracker;
#[cfg(not(fuzzing))]
pub(crate) type ActiveTracker = NoopTracker;
