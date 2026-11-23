/-!
# A minimal test harness

Tests are `TestM` actions that record named expectations. `runTests` prints a summary and returns
a non-zero exit code if any expectation failed, which is what `lake test` checks.
-/

namespace UUIDTest

/-- Accumulated test results. -/
structure Results where
  passed : Nat := 0
  failures : Array String := #[]

/-- The test monad: `IO` plus a record of results. -/
abbrev TestM := StateRefT Results IO

/-- Record an expectation. `detail` is only rendered when the expectation fails. -/
def expect (name : String) (ok : Bool) (detail : Unit → String := fun _ => "") : TestM Unit :=
  if ok then
    modify fun r => { r with passed := r.passed + 1 }
  else
    let d := detail ()
    let msg := if d.isEmpty then name else s!"{name}: {d}"
    modify fun r => { r with failures := r.failures.push msg }

/-- Expect two values to be equal, showing both on failure. -/
def expectEq {α : Type} [BEq α] [Repr α] (name : String) (actual expected : α) : TestM Unit :=
  expect name (actual == expected) fun _ =>
    s!"expected {repr expected}, got {repr actual}"

/-- Check `prop` on `count` random samples produced by `gen`. Stops at the first failure. -/
def forAll {α : Type} [Repr α] (name : String) (count : Nat) (gen : IO α) (prop : α → Bool) :
    TestM Unit := do
  for _ in [0:count] do
    let x ← gen
    unless prop x do
      expect name false fun _ => s!"counterexample: {repr x}"
      return
  expect name true

/-- Run a list of named test suites and return the process exit code. -/
def runTests (suites : List (String × TestM Unit)) : IO UInt32 := do
  let mut total : Results := {}
  for (name, suite) in suites do
    let ((), r) ← suite.run {}
    let status := if r.failures.isEmpty then "ok" else "FAILED"
    IO.println s!"[{status}] {name}: {r.passed} passed, {r.failures.size} failed"
    for f in r.failures do
      IO.println s!"    ✗ {f}"
    total := { passed := total.passed + r.passed, failures := total.failures ++ r.failures }
  IO.println s!"\n{total.passed} passed, {total.failures.size} failed"
  return if total.failures.isEmpty then 0 else 1

end UUIDTest
