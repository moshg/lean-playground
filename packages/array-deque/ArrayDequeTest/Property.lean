import ArrayDeque

/-!
Randomized model test: the same random operation sequence is applied to an `ArrayDeque Nat` and to a
`List Nat` model, and all observations are compared after every step.
-/

namespace ArrayDequeTest.Property

open ArrayDeque

/-- One step of the model test. `push` biases the choice towards pushes (growth phase: 60% push,
30% pop, 10% set) or pops (drain phase: 30% push, 60% pop, 10% set). -/
def step (push : Bool) (d : ArrayDeque Nat) (l : List Nat) (g : StdGen) :
    ArrayDeque Nat × List Nat × StdGen :=
  let (op, g) := randNat g 0 9
  let (v, g) := randNat g 0 1000
  let (i, g) := randNat g 0 (l.length + 1)
  let (side, g) := randNat g 0 1
  -- 0 pushBack, 1 pushFront, 2 popFront?, 3 popBack?, 4 popFront/popBack, 5 set
  let kind :=
    if op = 9 then 5
    else if push then (if op < 6 then side else 2 + op % 3)
    else (if op < 3 then side else 2 + op % 3)
  match kind with
  | 0 => (d.pushBack v, l ++ [v], g)
  | 1 => (d.pushFront v, v :: l, g)
  | 2 => let (_, d) := d.popFront?; (d, l.tail, g)
  | 3 => let (_, d) := d.popBack?; (d, l.dropLast, g)
  | 4 => if i % 2 = 0 then (d.popFront, l.tail, g) else (d.popBack, l.dropLast, g)
  | _ =>
    if h : i < d.size then (d.set i v h, l.set i v, g)
    else (d.setIfInBounds i v, l.set i v, g)

/-- Compares every observation of `d` with the model `l`. -/
def compare (d : ArrayDeque Nat) (l : List Nat) (i : Nat) : Except String Unit := do
  unless d.toList = l do throw s!"toList {d.toList} ≠ {l}"
  unless d.size = l.length do throw s!"size {d.size} ≠ {l.length}"
  unless d.isEmpty = l.isEmpty do throw "isEmpty"
  unless d.front? = l.head? do throw "front?"
  unless d.back? = l.getLast? do throw "back?"
  unless d.popFront?.1 = l.head? do throw "popFront?.1"
  unless d.popBack?.1 = l.getLast? do throw "popBack?.1"
  unless d[i]? = l[i]? do throw s!"getElem? {i}"
  unless d.toArray.toList = l do throw "toArray"
  unless d.foldl (fun acc x => acc * 31 + x) 7 = l.foldl (fun acc x => acc * 31 + x) 7 do
    throw "foldl"
  unless d.size ≤ d.capacity do throw "size ≤ capacity"
  unless d.capacity = 0 ∨ d.capacity.isPowerOfTwo do throw s!"capacity {d.capacity}"

/-- Runs `n` random steps from `seed`, switching between push and pop phases every 200 steps.
Returns the largest capacity reached, so that the caller can check that growth was exercised. -/
def checkRandom (seed n : Nat) : Except String Nat := do
  let mut d : ArrayDeque Nat := ∅
  let mut l : List Nat := []
  let mut g := mkStdGen seed
  let mut maxCap := 0
  for k in [0:n] do
    let (d', l', g') := step ((k / 200) % 2 = 0) d l g
    d := d'; l := l'; g := g'
    let (i, g') := randNat g 0 (l.length + 1)
    g := g'
    match compare d l i with
    | .ok () => pure ()
    | .error e => throw s!"seed {seed}, step {k}: {e}"
    maxCap := max maxCap d.capacity
  return maxCap

/-- Runs the model test for a fixed set of seeds. -/
def run : IO Bool := do
  let mut ok := true
  for seed in [0:20] do
    match checkRandom seed 2000 with
    | .ok maxCap =>
      if maxCap < 64 then
        IO.eprintln s!"property: seed {seed} only reached capacity {maxCap}"; ok := false
    | .error e => IO.eprintln s!"property: {e}"; ok := false
  return ok

end ArrayDequeTest.Property
