extern crate alloc;

use crate::test_harness::{run_ops, Op};
use crate::ScopedBump;
use alloc::vec;
use proptest::prelude::*;

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        4 => (0usize..=256, 0u8..=6).prop_map(|(size, align_pow2)| Op::Alloc { size, align_pow2 }),
        3 => (0usize..64).prop_map(|idx| Op::Dealloc { idx }),
        2 => (0usize..64, 0usize..=512).prop_map(|(idx, new_size)| Op::Realloc { idx, new_size }),
        1 => Just(Op::EnterScope),
        1 => Just(Op::ExitScope),
    ]
}

macro_rules! fuzz_proptest {
    ($name:ident, ring=$ring:literal, arena=$arena:literal, ops=$ops:expr, cases=$cases:literal) => {
        proptest! {
            #![proptest_config(ProptestConfig::with_cases($cases))]
            #[test]
            fn $name(ops in proptest::collection::vec(op_strategy(), $ops)) {
                let mut arena_buf = vec![0u8; $arena];
                let arena_base = arena_buf.as_ptr() as usize;
                let alloc = ScopedBump::<$ring>::new_uninit();
                unsafe { alloc.init(arena_buf.as_mut_ptr(), arena_buf.len()) };
                run_ops::<$ring>(&alloc, &ops, arena_base, $arena);
            }
        }
    };
}

fuzz_proptest!(
    random_ops,
    ring = 16,
    arena = 2048,
    ops = 1..500,
    cases = 3000
);
fuzz_proptest!(
    random_ops_small_ring,
    ring = 2,
    arena = 2048,
    ops = 1..300,
    cases = 2000
);
fuzz_proptest!(
    random_ops_tiny_arena,
    ring = 8,
    arena = 256,
    ops = 1..300,
    cases = 2000
);
fuzz_proptest!(
    random_ops_long,
    ring = 16,
    arena = 4096,
    ops = 200..1000,
    cases = 1000
);
