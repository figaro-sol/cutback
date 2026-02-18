#![no_main]

use arbitrary::Arbitrary;
use cutback::test_harness::{Op, run_ops};
use cutback::ScopedBump;
use libfuzzer_sys::fuzz_target;

#[derive(Debug, Arbitrary)]
enum FuzzOp {
    Alloc { size: u8, align_pow2: u8 },
    Dealloc { idx: u8 },
    Realloc { idx: u8, new_size: u16 },
    EnterScope,
    ExitScope,
}

impl From<FuzzOp> for Op {
    fn from(f: FuzzOp) -> Op {
        match f {
            FuzzOp::Alloc { size, align_pow2 } => Op::Alloc {
                size: size as usize,
                align_pow2: align_pow2 % 8, // clamp to 0..=7 (align 1..128)
            },
            FuzzOp::Dealloc { idx } => Op::Dealloc { idx: idx as usize },
            FuzzOp::Realloc { idx, new_size } => Op::Realloc {
                idx: idx as usize,
                new_size: new_size as usize,
            },
            FuzzOp::EnterScope => Op::EnterScope,
            FuzzOp::ExitScope => Op::ExitScope,
        }
    }
}

/// Wraps all fuzz inputs so libfuzzer can vary both the ring size and op sequence.
#[derive(Debug, Arbitrary)]
struct FuzzInput {
    /// Selects arena/ring configuration: 0→ring=2 (stress eviction), 1→ring=8, 2+→ring=16.
    ring_sel: u8,
    ops: Vec<FuzzOp>,
}

/// Instantiate a fresh allocator with ring size `N` and run the op sequence.
fn run_fuzz_ops<const N: usize>(ops: &[Op], arena_size: usize) {
    let mut arena = vec![0u8; arena_size];
    let arena_base = arena.as_ptr() as usize;
    let alloc = ScopedBump::<N>::new_uninit();
    unsafe { alloc.init(arena.as_mut_ptr(), arena.len()) };
    run_ops::<N>(&alloc, ops, arena_base, arena_size);
}

fuzz_target!(|input: FuzzInput| {
    let ops: Vec<Op> = input.ops.into_iter().map(Op::from).collect();
    match input.ring_sel % 3 {
        0 => run_fuzz_ops::<2>(&ops, 2048),  // small ring: stresses eviction aggressively
        1 => run_fuzz_ops::<8>(&ops, 2048),  // moderate eviction, 2K arena
        _ => run_fuzz_ops::<16>(&ops, 4096), // large ring + arena, long sequences
    }
});
