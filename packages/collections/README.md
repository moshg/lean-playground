# collections

Data structures, each specified against a simple model with machine-checked proofs (no `sorry`).
Everything lives in `namespace Collections`; `import Collections` brings in all of them, or import
a single module such as `Collections.ArrayDeque`.

| Module | Summary |
|---|---|
| `Collections.ArrayDeque` | Double-ended queue backed by a growable ring buffer over `Array` |

```toml
[[require]]
name = "collections"
git = "https://github.com/moshg/lean-playground"
rev = "main"
subDir = "packages/collections"
```

## ArrayDeque

A double-ended queue `ArrayDeque α` backed by a growable ring buffer over `Array`, like Rust's
`VecDeque`. Pushing and popping at either end take amortized O(1) time, and an unshared deque is
updated in place.

```lean
import Collections.ArrayDeque
open Collections

def demo : Option Nat × List Nat :=
  let d : ArrayDeque Nat := ((∅ : ArrayDeque Nat).pushBack 1).pushBack 2 |>.pushFront 0
  let (x?, d) := d.popFront?   -- (some 0, [1, 2])
  (x?, d.toList)
```

- Operations that create or free slots (`pushBack`/`pushFront`, the pops, `ofList`,
  `emptyWithCapacity`) need `[Inhabited α]`: empty slots hold `default`, and popped slots are reset
  so the deque does not keep popped elements alive.
- `popFront?`/`popBack?` return `Option α × ArrayDeque α`, the deque included even when empty. Bind
  the result and drop the old deque (`let (x?, d) := d.popFront?`) to keep updates in place.
- Every operation is specified against `toList` in `Collections.ArrayDeque.Lemmas`
  (e.g. `toList_pushBack : (d.pushBack x).toList = d.toList ++ [x]`), with no `sorry`.

The design notes are in [`docs/design/array-deque.md`](../../docs/design/array-deque.md).
