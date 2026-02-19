#[allow(dead_code)]
mod recent {
    use modular_bitfield::prelude::*;
    #[bitfield(bits = 64)]
    #[derive(Copy, Clone)]
    pub(crate) struct RecentAlloc {
        pub size: B30,   // bits  0-29: allocation size (max 1 GB)
        pub offset: B30, // bits 30-59: arena offset   (max 1 GB)
        #[skip]
        __: B3, // bits 60-62: padding
        pub alive: bool, // bit  63
    }
}

use recent::RecentAlloc;

// SAFETY: modular-bitfield uses repr([u8; 8]); all-zero bytes = alive=0 (dead)
const DEAD_ALLOC: RecentAlloc = unsafe { core::mem::transmute::<[u8; 8], RecentAlloc>([0u8; 8]) };

#[derive(Copy, Clone)]
pub(crate) struct RingBuffer<const N: usize> {
    buf: [RecentAlloc; N],
    head: usize,
    len: usize,
}

impl<const N: usize> RingBuffer<N> {
    pub const fn new() -> Self {
        const { assert!(N >= 1) };
        Self {
            buf: [DEAD_ALLOC; N],
            head: 0,
            len: 0,
        }
    }

    pub fn push(&mut self, offset: usize, size: usize) {
        self.buf[self.head] = RecentAlloc::new()
            .with_offset(offset as u32)
            .with_size(size as u32)
            .with_alive(true);
        self.head = (self.head + 1) % N;
        if self.len < N {
            self.len += 1;
        }
    }

    /// Scan newest-to-oldest, return index of first alive entry matching offset.
    pub fn find_by_offset(&self, offset: usize) -> Option<usize> {
        for i in 0..self.len {
            let idx = (self.head + N - 1 - i) % N;
            let entry = &self.buf[idx];
            if entry.alive() && entry.offset() as usize == offset {
                return Some(idx);
            }
        }
        None
    }

    pub fn mark_dead(&mut self, idx: usize) {
        self.buf[idx].set_alive(false);
    }

    /// Return a reference to the newest entry, if any.
    pub fn newest(&self) -> Option<&RecentAlloc> {
        if self.len == 0 {
            return None;
        }
        Some(&self.buf[(self.head + N - 1) % N])
    }

    /// Update the size of the newest entry.
    pub fn update_newest_size(&mut self, new_size: usize) {
        debug_assert!(self.len > 0);
        let idx = (self.head + N - 1) % N;
        self.buf[idx].set_size(new_size as u32);
    }

    /// Mark all entries with offset >= `from_offset` as dead.
    #[cfg(test)]
    pub fn invalidate_from_offset(&mut self, from_offset: usize) {
        for i in 0..self.len {
            let idx = (self.head + N - 1 - i) % N;
            if self.buf[idx].offset() as usize >= from_offset {
                self.buf[idx].set_alive(false);
            }
        }
    }

    /// Walk newest-to-oldest. While entries are dead, track the lowest offset seen.
    /// Stop at the first alive entry. Returns the offset to rewind cursor to,
    /// or None if no dead suffix exists at the tail.
    pub fn suffix_rewind_cursor(&self) -> Option<usize> {
        let mut rewind_to: Option<usize> = None;
        for i in 0..self.len {
            let idx = (self.head + N - 1 - i) % N;
            let entry = &self.buf[idx];
            if entry.alive() {
                break;
            }
            rewind_to = Some(match rewind_to {
                Some(prev) => prev.min(entry.offset() as usize),
                None => entry.offset() as usize,
            });
        }
        rewind_to
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recent_alloc_is_8_bytes() {
        assert_eq!(core::mem::size_of::<RecentAlloc>(), 8);
    }

    #[test]
    fn new_ring_is_empty() {
        let ring = RingBuffer::<4>::new();
        assert_eq!(ring.len, 0);
        assert_eq!(ring.head, 0);
    }

    #[test]
    fn push_and_len() {
        let mut ring = RingBuffer::<4>::new();
        ring.push(0, 8);
        assert_eq!(ring.len, 1);
        ring.push(8, 8);
        assert_eq!(ring.len, 2);
        ring.push(16, 8);
        ring.push(24, 8);
        assert_eq!(ring.len, 4);
        // 5th push wraps, len stays at N
        ring.push(32, 8);
        assert_eq!(ring.len, 4);
    }

    #[test]
    fn push_overwrites_oldest() {
        let mut ring = RingBuffer::<2>::new();
        ring.push(0, 8);
        ring.push(8, 8);
        ring.push(16, 8);
        // oldest (offset=0) is gone, offset=8 is now oldest
        assert!(ring.find_by_offset(0).is_none());
        assert!(ring.find_by_offset(8).is_some());
        assert!(ring.find_by_offset(16).is_some());
    }

    #[test]
    fn find_by_offset_skips_dead() {
        let mut ring = RingBuffer::<4>::new();
        ring.push(0, 8);
        ring.push(8, 8);
        let idx = ring.find_by_offset(0).unwrap();
        ring.mark_dead(idx);
        assert!(ring.find_by_offset(0).is_none());
        assert!(ring.find_by_offset(8).is_some());
    }

    #[test]
    fn find_by_offset_miss() {
        let mut ring = RingBuffer::<4>::new();
        ring.push(0, 8);
        assert!(ring.find_by_offset(99).is_none());
    }

    #[test]
    fn suffix_rewind_all_dead() {
        let mut ring = RingBuffer::<4>::new();
        ring.push(0, 8);
        ring.push(8, 8);
        let i0 = ring.find_by_offset(0).unwrap();
        let i1 = ring.find_by_offset(8).unwrap();
        ring.mark_dead(i0);
        ring.mark_dead(i1);
        assert_eq!(ring.suffix_rewind_cursor(), Some(0));
    }

    #[test]
    fn suffix_rewind_none_dead() {
        let mut ring = RingBuffer::<4>::new();
        ring.push(0, 8);
        ring.push(8, 8);
        assert_eq!(ring.suffix_rewind_cursor(), None);
    }

    #[test]
    fn suffix_rewind_partial() {
        let mut ring = RingBuffer::<4>::new();
        ring.push(0, 8); // oldest
        ring.push(8, 8);
        ring.push(16, 8); // newest
                          // kill newest only
        let idx = ring.find_by_offset(16).unwrap();
        ring.mark_dead(idx);
        assert_eq!(ring.suffix_rewind_cursor(), Some(16));
        // kill middle too
        let idx = ring.find_by_offset(8).unwrap();
        ring.mark_dead(idx);
        assert_eq!(ring.suffix_rewind_cursor(), Some(8));
    }

    #[test]
    fn invalidate_from_offset() {
        let mut ring = RingBuffer::<4>::new();
        ring.push(0, 8);
        ring.push(8, 8);
        ring.push(16, 8);
        ring.invalidate_from_offset(8);
        assert!(ring.find_by_offset(0).is_some());
        assert!(ring.find_by_offset(8).is_none());
        assert!(ring.find_by_offset(16).is_none());
    }

    #[test]
    fn newest_empty() {
        let ring = RingBuffer::<4>::new();
        assert!(ring.newest().is_none());
    }

    #[test]
    fn newest_returns_last_pushed() {
        let mut ring = RingBuffer::<4>::new();
        ring.push(0, 8);
        ring.push(8, 16);
        let n = ring.newest().unwrap();
        assert_eq!(n.offset() as usize, 8);
        assert_eq!(n.size() as usize, 16);
    }

    #[test]
    fn update_newest_size() {
        let mut ring = RingBuffer::<4>::new();
        ring.push(0, 8);
        ring.update_newest_size(32);
        assert_eq!(ring.newest().unwrap().size() as usize, 32);
    }

    #[test]
    fn single_slot_ring() {
        let mut ring = RingBuffer::<1>::new();
        ring.push(0, 8);
        assert_eq!(ring.len, 1);
        assert!(ring.find_by_offset(0).is_some());
        // overwrite
        ring.push(8, 8);
        assert_eq!(ring.len, 1);
        assert!(ring.find_by_offset(0).is_none());
        assert!(ring.find_by_offset(8).is_some());
    }
}
