# cutback

A bump allocator that can actually give memory back.

Standard bump allocators are fast but wasteful -- once you allocate, that memory is gone until you reset the whole arena. Cutback tracks recent allocations in a small ring buffer so it can rewind the cursor when you deallocate in LIFO order. If you allocate A, B, C and then free C, the cursor moves back and that space is reusable immediately.

When deallocations happen out of order, cutback behaves like a normal bump allocator -- the space sticks around until you do a mark/reset. No linked lists, no per-allocation headers in the arena.

## How it works

The allocator maintains a cursor into a contiguous byte arena. Allocations advance the cursor forward. A fixed-size ring buffer (the const generic `N`) remembers the last N allocations. On dealloc, if the freed block is at the tail of the arena, the cursor rewinds.

Mark/reset gives you scoped allocation: save the cursor position, do a bunch of work, then reset to reclaim everything at once.

```
alloc A (0..64)    cursor=64   ring=[A]
alloc B (64..128)  cursor=128  ring=[A, B]
alloc C (128..192) cursor=192  ring=[A, B, C]
dealloc C          cursor=128  ring=[A, B]       <- cursor rewinds
dealloc A          cursor=128  ring=[_, B]       <- can't rewind, B is in the way
dealloc B          cursor=0    ring=[]            <- now both A and B rewind
```

## Usage

```rust
use cutback::ScopedBump;
use core::alloc::{GlobalAlloc, Layout};

// Provide your own memory. Stack, static, mmap -- whatever you want.
let mut arena = [0u8; 4096];
let alloc = ScopedBump::<8>::new_uninit();  // 8-slot ring buffer
unsafe { alloc.init(arena.as_mut_ptr(), arena.len()) };

let layout = Layout::from_size_align(64, 8).unwrap();
unsafe {
    let ptr = alloc.alloc(layout);
    // use it...
    alloc.dealloc(ptr, layout);  // cursor rewinds, space is free
}
```

### Mark/reset

```rust
let mark = alloc.mark();
unsafe {
    let a = alloc.alloc(layout);
    let b = alloc.alloc(layout);
    // ...
    alloc.reset(mark);  // both a and b are gone, cursor back to where it was
}
```

### As a global allocator

```rust
use cutback::ScopedBump;

#[global_allocator]
static ALLOC: ScopedBump<32> = ScopedBump::new_uninit();

fn main() {
    // init with a static or heap-backed buffer before any allocations
    let arena: &mut [u8] = /* your memory source */;
    unsafe { ALLOC.init(arena.as_mut_ptr(), arena.len()) };
}
```

`ScopedBump::new_uninit()` is const, so it works in statics. The `init` call has to happen before anything allocates.

## Design

The const generic `N` controls ring buffer size -- how many recent allocations get tracked. Anything older than N slots is "forgotten." Still valid memory, but dealloc can't rewind the cursor for it anymore. Pick N based on your workload: smaller means less metadata, larger means more deallocations can reclaim space.

The crate is `no_std` with zero dependencies (only `core`). Works on embedded, in kernels, wherever.

This is a single-threaded allocator. The `Sync` impl exists so you can put it in a static, but concurrent access from multiple threads is undefined behavior.

A few edge cases worth knowing about: ZST allocations return a dangling aligned pointer and don't touch the arena or ring buffer. If you dealloc a pointer that didn't come from this arena, it's silently ignored. And if you realloc the most recent allocation and it fits, cutback extends it in place without copying.

## API

| Function | What it does |
|----------|-------------|
| `ScopedBump::<N>::new_uninit()` | Create an uninitialized allocator (const) |
| `init(base, cap)` | Point the allocator at your memory region |
| `alloc(layout)` | Allocate memory |
| `dealloc(ptr, layout)` | Free memory (may rewind cursor) |
| `realloc(ptr, layout, new_size)` | Resize (in-place when possible) |
| `mark()` | Save current cursor position |
| `reset(mark)` | Rewind to a saved position |

## When to use this

Cutback is a good fit when you have short-lived allocation scopes with mostly-LIFO patterns. Parsers, serializers, frame allocators in games, temporary computation buffers -- anywhere you'd use a bump allocator but wish you could get some memory back without resetting everything.

It's not a general-purpose allocator. If your allocation patterns are random or long-lived, use something else.

## Testing

The crate has ~50 unit tests covering the allocator and ring buffer, plus property-based tests using proptest that throw random sequences of alloc/dealloc/realloc/mark/reset at both the real allocator and a reference model, then check for invariant violations (overlapping allocations, out-of-bounds, data corruption, alignment errors).

```
cargo test
```

## License

MIT
