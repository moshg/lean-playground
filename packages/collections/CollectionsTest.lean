import CollectionsTest.ArrayDeque.Basic
import CollectionsTest.ArrayDeque.Axioms
import CollectionsTest.ArrayDeque.Property
import CollectionsTest.ArrayDeque.InPlace

def main : IO UInt32 := do
  let p ← CollectionsTest.ArrayDeque.Property.run
  let i ← CollectionsTest.ArrayDeque.InPlace.run
  if p && i then
    IO.println "All Collections tests passed."
    return 0
  else
    return 1
