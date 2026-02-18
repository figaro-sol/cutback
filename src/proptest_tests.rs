extern crate alloc;

use crate::bump::MarkNode;
use crate::ScopedBump;
use alloc::vec;
use alloc::vec::Vec;
use core::alloc::{GlobalAlloc, Layout};
use proptest::prelude::*;

const ARENA_SIZE: usize = 2048;
const RING_SIZE: usize = 16;

#[derive(Debug, Clone)]
enum Op {
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

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        4 => (0usize..=256, 0u8..=6).prop_map(|(size, align_pow2)| Op::Alloc { size, align_pow2 }),
        3 => (0usize..64).prop_map(|idx| Op::Dealloc { idx }),
        2 => (0usize..64, 0usize..=512).prop_map(|(idx, new_size)| Op::Realloc { idx, new_size }),
        1 => Just(Op::EnterScope),
        1 => Just(Op::ExitScope),
    ]
}

fn check_invariants(allocs: &[ModelAlloc], arena_base: usize, arena_size: usize) {
    let alive: Vec<&ModelAlloc> = allocs.iter().filter(|a| a.alive).collect();
    for a in &alive {
        if a.layout.size() == 0 {
            assert_eq!((a.ptr as usize) % a.layout.align(), 0, "ZST misaligned");
            continue;
        }
        let ptr = a.ptr as usize;
        assert!(ptr >= arena_base, "ptr below arena base");
        assert!(
            ptr + a.layout.size() <= arena_base + arena_size,
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
    // check no overlaps (skip ZSTs)
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

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn random_ops(ops in proptest::collection::vec(op_strategy(), 1..100)) {
        let mut arena = vec![0u8; ARENA_SIZE];
        let arena_base = arena.as_ptr() as usize;
        let alloc = ScopedBump::<RING_SIZE>::new_uninit();
        unsafe { alloc.init(arena.as_mut_ptr(), arena.len()) };

        let mut allocs: Vec<ModelAlloc> = Vec::new();
        let mut scope_stack: Vec<u64> = Vec::new();
        let mut fill_counter: u8 = 1;
        let mut generation: u64 = 0;
        let mut mark_nodes: [MarkNode; 8] = core::array::from_fn(|_| MarkNode::uninit());
        let mut scope_depth: usize = 0;

        for op in ops {
            match op {
                Op::Alloc { size, align_pow2 } => {
                    let align = 1usize << (align_pow2 as usize);
                    let layout = match Layout::from_size_align(size, align) {
                        Ok(l) => l,
                        Err(_) => continue,
                    };
                    let ptr = unsafe { alloc.alloc(layout) };
                    if !ptr.is_null() {
                        if size == 0 {
                            assert_eq!((ptr as usize) % align, 0, "ZST misaligned");
                            generation += 1;
                            allocs.push(ModelAlloc {
                                ptr,
                                layout,
                                alive: true,
                                fill_byte: 0,
                                generation,
                            });
                            continue;
                        }
                        unsafe { core::ptr::write_bytes(ptr, fill_counter, size) };
                        generation += 1;
                        allocs.push(ModelAlloc {
                            ptr,
                            layout,
                            alive: true,
                            fill_byte: fill_counter,
                            generation,
                        });
                        fill_counter = fill_counter.wrapping_add(1);
                        if fill_counter == 0 {
                            fill_counter = 1;
                        }
                    }
                }
                Op::Dealloc { idx } => {
                    let alive_indices: Vec<usize> = allocs
                        .iter()
                        .enumerate()
                        .filter(|(_, a)| a.alive)
                        .map(|(i, _)| i)
                        .collect();
                    if alive_indices.is_empty() {
                        continue;
                    }
                    let target = alive_indices[idx % alive_indices.len()];
                    let a = &allocs[target];
                    for i in 0..a.layout.size() {
                        let byte = unsafe { *a.ptr.add(i) };
                        assert_eq!(byte, a.fill_byte);
                    }
                    unsafe { alloc.dealloc(a.ptr, a.layout) };
                    allocs[target].alive = false;
                }
                Op::Realloc { idx, new_size } => {
                    let alive_indices: Vec<usize> = allocs
                        .iter()
                        .enumerate()
                        .filter(|(_, a)| a.alive)
                        .map(|(i, _)| i)
                        .collect();
                    if alive_indices.is_empty() {
                        continue;
                    }
                    let target = alive_indices[idx % alive_indices.len()];
                    let a = &allocs[target];
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
                        allocs[target].alive = false;
                        continue;
                    }
                    let new_ptr = unsafe { alloc.realloc(a.ptr, a.layout, new_size) };
                    if !new_ptr.is_null() {
                        let preserved = old_size.min(new_size);
                        for i in 0..preserved {
                            let byte = unsafe { *new_ptr.add(i) };
                            assert_eq!(byte, old_fill);
                        }
                        let new_layout =
                            Layout::from_size_align(new_size, a.layout.align()).unwrap();
                        unsafe { core::ptr::write_bytes(new_ptr, fill_counter, new_size) };
                        generation += 1;
                        allocs[target] = ModelAlloc {
                            ptr: new_ptr,
                            layout: new_layout,
                            alive: true,
                            fill_byte: fill_counter,
                            generation,
                        };
                        fill_counter = fill_counter.wrapping_add(1);
                        if fill_counter == 0 {
                            fill_counter = 1;
                        }
                    }
                }
                Op::EnterScope => {
                    if scope_depth >= 8 {
                        continue;
                    }
                    unsafe { alloc.push_mark(&mut mark_nodes[scope_depth]) };
                    scope_stack.push(generation);
                    scope_depth += 1;
                }
                Op::ExitScope => {
                    if scope_stack.is_empty() {
                        continue;
                    }
                    unsafe { alloc.pop_mark_and_reset() };
                    scope_depth -= 1;
                    let saved_gen = scope_stack.pop().unwrap();
                    for a in allocs.iter_mut() {
                        if a.generation > saved_gen {
                            a.alive = false;
                        }
                    }
                }
            }
            check_invariants(&allocs, arena_base, ARENA_SIZE);
        }

        // cleanup: pop all remaining scopes
        while let Some(saved_gen) = scope_stack.pop() {
            unsafe { alloc.pop_mark_and_reset() };
            for a in allocs.iter_mut() {
                if a.generation > saved_gen {
                    a.alive = false;
                }
            }
        }
        check_invariants(&allocs, arena_base, ARENA_SIZE);
    }
}
