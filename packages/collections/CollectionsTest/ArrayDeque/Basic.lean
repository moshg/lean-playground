import Collections

/-! Small, hand-checked cases. Each expected list follows from the List model by hand. -/

namespace CollectionsTest.ArrayDeque.Basic

open Collections ArrayDeque

-- Empty deque
#guard (∅ : ArrayDeque Nat).toList = []
#guard (∅ : ArrayDeque Nat).capacity = 0
#guard (∅ : ArrayDeque Nat).isEmpty
#guard (∅ : ArrayDeque Nat).popFront?.1 = none
#guard (∅ : ArrayDeque Nat).popBack?.1 = none
#guard (∅ : ArrayDeque Nat).front? = none
#guard (∅ : ArrayDeque Nat).back? = none
#guard (∅ : ArrayDeque Nat).popFront.toList = []

-- Capacities are 0 or the next power of two
#guard (emptyWithCapacity 0 : ArrayDeque Nat).capacity = 0
#guard (emptyWithCapacity 1 : ArrayDeque Nat).capacity = 1
#guard (emptyWithCapacity 5 : ArrayDeque Nat).capacity = 8
#guard (emptyWithCapacity 8 : ArrayDeque Nat).capacity = 8
#guard (ofList ([] : List Nat)).capacity = 0
#guard (ofList [1, 2, 3]).capacity = 4
#guard (ofList [1, 2, 3]).toList = [1, 2, 3]

-- The first push into a capacity-0 deque grows it to 4
#guard ((∅ : ArrayDeque Nat).pushBack 1).capacity = 4
#guard ((∅ : ArrayDeque Nat).pushFront 1).toList = [1]
#guard ((∅ : ArrayDeque Nat).pushFront 1).head = 3

/-- A full deque whose elements wrap around the end of the buffer:
physical layout `[5, 6, 3, 4]` with `head = 2`. -/
def wrapped : ArrayDeque Nat :=
  ((((((((emptyWithCapacity 4).pushBack 1).pushBack 2).pushBack 3).popFront).popFront).pushBack
    4).pushBack 5).pushBack 6

#guard wrapped.toList = [3, 4, 5, 6]
#guard wrapped.capacity = 4
#guard wrapped.head = 2
#guard wrapped.buf = #[5, 6, 3, 4]
#guard wrapped.front? = some 3
#guard wrapped.back? = some 6
#guard (List.range 5).map (wrapped[·]?) = [some 3, some 4, some 5, some 6, none]

-- Growing a full, wrapped deque re-packs it from index 0
#guard (wrapped.pushBack 7).toList = [3, 4, 5, 6, 7]
#guard (wrapped.pushBack 7).capacity = 8
#guard (wrapped.pushBack 7).head = 0
#guard (wrapped.pushFront 2).toList = [2, 3, 4, 5, 6]
#guard (wrapped.pushFront 2).capacity = 8

-- Pops across the wrap point; freed slots are reset to `default`
#guard wrapped.popBack?.1 = some 6
#guard wrapped.popBack?.2.toList = [3, 4, 5]
#guard wrapped.popBack?.2.buf = #[5, 0, 3, 4]
#guard wrapped.popFront?.1 = some 3
#guard wrapped.popFront?.2.toList = [4, 5, 6]
#guard wrapped.popFront?.2.buf = #[5, 6, 0, 4]
#guard (wrapped.popFront.popFront.popFront).head = 1

-- pushFront wraps the head from 0 to capacity - 1
#guard (((emptyWithCapacity 4 : ArrayDeque Nat).pushBack 1).pushFront 0).head = 3
#guard (((emptyWithCapacity 4 : ArrayDeque Nat).pushBack 1).pushFront 0).toList = [0, 1]

-- set across the wrap point (`setIfInBounds`: `get_elem_tactic` cannot see through `capFor`)
#guard (wrapped.setIfInBounds 3 60).toList = [3, 4, 5, 60]
#guard (wrapped.setIfInBounds 3 60).buf = #[5, 60, 3, 4]
#guard (wrapped.setIfInBounds 4 60).toList = [3, 4, 5, 6]
#guard ((ofList [1, 2, 3]).set 2 9).toList = [1, 2, 9]

-- Traversal
#guard wrapped.foldl (fun acc x => acc * 10 + x) 0 = 3456
#guard wrapped.toArray = #[3, 4, 5, 6]
#guard (Id.run do
  let mut acc := []
  for x in wrapped do
    if x = 5 then break
    acc := x :: acc
  return acc) = [4, 3]

#guard reprStr (ofList [1, 2]) = "Collections.ArrayDeque.ofList [1, 2]"

end CollectionsTest.ArrayDeque.Basic
