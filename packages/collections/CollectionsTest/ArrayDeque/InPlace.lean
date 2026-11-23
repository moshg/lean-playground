import Collections

/-!
Checks that updates on an unshared deque modify its buffer in place, by comparing the buffer's
address before and after each operation.

Each check builds its deque from a distinct runtime value: a deque built from literals would be
hoisted into a shared global constant, and identical pure calls would be merged into one shared
value, either of which makes a correct implementation look like it copies.
-/

namespace CollectionsTest.ArrayDeque.InPlace

open Collections ArrayDeque

unsafe def bufAddrImpl (d : ArrayDeque Nat) : USize := ptrAddrUnsafe d.buf

/-- The address of the deque's buffer. -/
@[implemented_by bufAddrImpl] opaque bufAddr (d : ArrayDeque Nat) : USize

/-- A deque with `n` elements and capacity 64, so that the checked pushes do not grow it. -/
@[noinline] def mk (n : Nat) : ArrayDeque Nat := Id.run do
  let mut d : ArrayDeque Nat := emptyWithCapacity 64
  for i in [0:n] do d := d.pushBack i
  return d

/-- A deque of capacity 64 whose elements wrap around the end of the buffer (`head = 40`). -/
@[noinline] def mkWrapped (n : Nat) : ArrayDeque Nat := Id.run do
  let mut d : ArrayDeque Nat := emptyWithCapacity 64
  for i in [0:60] do d := d.pushBack i
  for _ in [0:40] do d := d.popFront
  for i in [0:n] do d := d.pushBack i
  return d

/-- Whether `op` keeps the buffer of `d` in place. -/
@[noinline] def inPlace (d : ArrayDeque Nat) (op : ArrayDeque Nat → ArrayDeque Nat) : Bool :=
  let a := bufAddr d
  let d' := op d
  bufAddr d' == a

/-- Runs all checks; `n` must come from a runtime value. -/
def checks (n : Nat) : List (String × Bool) :=
  [ ("pushBack", inPlace (mk (n + 1)) (·.pushBack 7)),
    ("pushFront", inPlace (mk (n + 2)) (·.pushFront 7)),
    ("popFront?", inPlace (mk (n + 3)) (fun d => let (_, d) := d.popFront?; d)),
    ("popBack?", inPlace (mk (n + 4)) (fun d => let (_, d) := d.popBack?; d)),
    ("popFront", inPlace (mk (n + 5)) (·.popFront)),
    ("popBack", inPlace (mk (n + 6)) (·.popBack)),
    ("setIfInBounds", inPlace (mk (n + 7)) (·.setIfInBounds 1 9)),
    ("set", inPlace (mk (n + 8)) (fun d => if h : 1 < d.size then d.set 1 9 h else d)),
    ("wrapped pushBack", inPlace (mkWrapped (n + 11)) (·.pushBack 7)),
    ("wrapped pushFront", inPlace (mkWrapped (n + 12)) (·.pushFront 7)),
    ("wrapped popFront?", inPlace (mkWrapped (n + 13)) (fun d => let (_, d) := d.popFront?; d)),
    ("wrapped popBack?", inPlace (mkWrapped (n + 14)) (fun d => let (_, d) := d.popBack?; d)),
    ("wrapped set", inPlace (mkWrapped (n + 15)) (·.setIfInBounds 25 9)),
    -- An odd number of pops: with an even number, a copying implementation could get the original
    -- address back from the allocator.
    ("pop loop", inPlace (mk (n + 9)) fun d => Id.run do
      let mut d := d
      for _ in [0:3] do
        let (_, d') := d.popFront?
        d := d'
      return d) ]

/-- Runs the in-place checks. -/
def run : IO Bool := do
  -- A value the compiler cannot constant-fold.
  let n := 10 + (← IO.monoNanosNow) % 1
  let mut ok := true
  -- The wrapped deques must actually wrap: head 40, 30+ elements, capacity 64.
  let w := mkWrapped (n + 10)
  unless w.head = 40 && w.capacity = 64 && w.size ≥ 30 do
    IO.eprintln "in-place: mkWrapped does not wrap"; ok := false
  for (name, b) in checks n do
    unless b do IO.eprintln s!"in-place: {name} copied its buffer"; ok := false
  return ok

end CollectionsTest.ArrayDeque.InPlace
