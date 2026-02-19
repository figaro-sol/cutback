extern crate alloc;

use alloc::vec::Vec;
use core::alloc::{GlobalAlloc, Layout};

use crate::ScopedBump;

#[derive(Debug, Clone)]
pub enum Op {
    Alloc { size: usize, align_pow2: u8 },
    Dealloc { idx: usize },
    Realloc { idx: usize, new_size: usize },
    EnterScope,
    ExitScope,
}

#[derive(Debug)]
struct ModelAlloc {
    ptr: *mut u8,
    layout: Layout,
    alive: bool,
    fill_byte: u8,
    generation: u64,
}

struct ModelState {
    allocs: Vec<ModelAlloc>,
    fill_counter: u8,
    generation: u64,
    arena_base: usize,
    arena_size: usize,
}

impl ModelState {
    fn new(arena_base: usize, arena_size: usize) -> Self {
        Self {
            allocs: Vec::new(),
            fill_counter: 1,
            generation: 0,
            arena_base,
            arena_size,
        }
    }

    fn next_fill(&mut self) -> u8 {
        let fill = self.fill_counter;
        self.fill_counter = self.fill_counter.wrapping_add(1);
        if self.fill_counter == 0 {
            self.fill_counter = 1;
        }
        fill
    }

    fn check_invariants(&self) {
        let alive: Vec<&ModelAlloc> = self.allocs.iter().filter(|a| a.alive).collect();
        for a in &alive {
            if a.layout.size() == 0 {
                assert_eq!((a.ptr as usize) % a.layout.align(), 0, "ZST misaligned");
                continue;
            }
            let ptr = a.ptr as usize;
            assert!(ptr >= self.arena_base, "ptr below arena base");
            assert!(
                ptr + a.layout.size() <= self.arena_base + self.arena_size,
                "alloc exceeds arena"
            );
            assert_eq!(ptr % a.layout.align(), 0, "misaligned allocation");
            for i in 0..a.layout.size() {
                let byte = unsafe { *a.ptr.add(i) };
                assert_eq!(
                    byte, a.fill_byte,
                    "data corruption at offset {} in alloc at {:p}",
                    i, a.ptr
                );
            }
        }
        let sized_alive: Vec<&ModelAlloc> = alive
            .iter()
            .filter(|a| a.layout.size() > 0)
            .copied()
            .collect();
        for i in 0..sized_alive.len() {
            for j in (i + 1)..sized_alive.len() {
                let a_start = sized_alive[i].ptr as usize;
                let a_end = a_start + sized_alive[i].layout.size();
                let b_start = sized_alive[j].ptr as usize;
                let b_end = b_start + sized_alive[j].layout.size();
                assert!(
                    a_end <= b_start || b_end <= a_start,
                    "overlap: [{:#x}..{:#x}) and [{:#x}..{:#x})",
                    a_start,
                    a_end,
                    b_start,
                    b_end
                );
            }
        }
    }

    fn handle_alloc<const N: usize>(&mut self, alloc: &ScopedBump<N>, size: usize, align_pow2: u8) {
        let align = 1usize << (align_pow2 as usize);
        let layout = match Layout::from_size_align(size, align) {
            Ok(l) => l,
            Err(_) => return,
        };
        let ptr = unsafe { alloc.alloc(layout) };
        if ptr.is_null() {
            return;
        }
        if size == 0 {
            assert_eq!((ptr as usize) % align, 0, "ZST misaligned");
            self.generation += 1;
            self.allocs.push(ModelAlloc {
                ptr,
                layout,
                alive: true,
                fill_byte: 0,
                generation: self.generation,
            });
            return;
        }
        let fill = self.next_fill();
        unsafe { core::ptr::write_bytes(ptr, fill, size) };
        self.generation += 1;
        self.allocs.push(ModelAlloc {
            ptr,
            layout,
            alive: true,
            fill_byte: fill,
            generation: self.generation,
        });
    }

    fn handle_dealloc<const N: usize>(&mut self, alloc: &ScopedBump<N>, idx: usize) {
        let alive_indices: Vec<usize> = self
            .allocs
            .iter()
            .enumerate()
            .filter(|(_, a)| a.alive)
            .map(|(i, _)| i)
            .collect();
        if alive_indices.is_empty() {
            return;
        }
        let target = alive_indices[idx % alive_indices.len()];
        let a = &self.allocs[target];
        for i in 0..a.layout.size() {
            let byte = unsafe { *a.ptr.add(i) };
            assert_eq!(byte, a.fill_byte);
        }
        unsafe { alloc.dealloc(a.ptr, a.layout) };
        self.allocs[target].alive = false;
    }

    fn handle_realloc<const N: usize>(
        &mut self,
        alloc: &ScopedBump<N>,
        idx: usize,
        new_size: usize,
    ) {
        let alive_indices: Vec<usize> = self
            .allocs
            .iter()
            .enumerate()
            .filter(|(_, a)| a.alive)
            .map(|(i, _)| i)
            .collect();
        if alive_indices.is_empty() {
            return;
        }
        let target = alive_indices[idx % alive_indices.len()];
        let a = &self.allocs[target];
        let old_size = a.layout.size();
        let old_fill = a.fill_byte;
        for i in 0..old_size {
            let byte = unsafe { *a.ptr.add(i) };
            assert_eq!(byte, old_fill);
        }
        if new_size == 0 {
            let new_ptr = unsafe { alloc.realloc(a.ptr, a.layout, 0) };
            assert!(!new_ptr.is_null(), "realloc to ZST returned null");
            assert_eq!((new_ptr as usize) % a.layout.align(), 0, "ZST misaligned");
            self.allocs[target].alive = false;
            return;
        }
        let new_ptr = unsafe { alloc.realloc(a.ptr, a.layout, new_size) };
        if !new_ptr.is_null() {
            let preserved = old_size.min(new_size);
            for i in 0..preserved {
                let byte = unsafe { *new_ptr.add(i) };
                assert_eq!(byte, old_fill);
            }
            let new_layout = Layout::from_size_align(new_size, a.layout.align()).unwrap();
            let fill = self.next_fill();
            unsafe { core::ptr::write_bytes(new_ptr, fill, new_size) };
            self.generation += 1;
            self.allocs[target] = ModelAlloc {
                ptr: new_ptr,
                layout: new_layout,
                alive: true,
                fill_byte: fill,
                generation: self.generation,
            };
        }
    }

    fn invalidate_scope(&mut self, saved_gen: u64) {
        for a in self.allocs.iter_mut() {
            if a.generation > saved_gen {
                a.alive = false;
            }
        }
    }
}

pub fn run_ops<const N: usize>(
    alloc: &ScopedBump<N>,
    ops: &[Op],
    arena_base: usize,
    arena_size: usize,
) {
    let mut state = ModelState::new(arena_base, arena_size);
    run_scope(alloc, ops, &mut state, 0);
}

fn run_scope<'a, const N: usize>(
    alloc: &ScopedBump<N>,
    ops: &'a [Op],
    state: &mut ModelState,
    depth: usize,
) -> &'a [Op] {
    let mut ops = ops;
    while let Some((first, rest)) = ops.split_first() {
        ops = rest;
        match first {
            Op::Alloc { size, align_pow2 } => state.handle_alloc(alloc, *size, *align_pow2),
            Op::Dealloc { idx } => state.handle_dealloc(alloc, *idx),
            Op::Realloc { idx, new_size } => state.handle_realloc(alloc, *idx, *new_size),
            Op::EnterScope => {
                let saved_gen = state.generation;
                unsafe {
                    ops = alloc.with_mark(|| run_scope(alloc, ops, state, depth + 1));
                }
                state.invalidate_scope(saved_gen);
            }
            Op::ExitScope => {
                if depth > 0 {
                    return ops;
                }
            }
        }
        state.check_invariants();
    }
    ops
}
