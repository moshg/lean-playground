import ArrayDequeTest.Basic
import ArrayDequeTest.Axioms
import ArrayDequeTest.Property
import ArrayDequeTest.InPlace

def main : IO UInt32 := do
  let p ← ArrayDequeTest.Property.run
  let i ← ArrayDequeTest.InPlace.run
  if p && i then
    IO.println "All ArrayDeque tests passed."
    return 0
  else
    return 1
