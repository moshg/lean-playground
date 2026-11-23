import ArrayDeque

/-! The specification theorems use no `sorry` and no axioms beyond the standard ones. -/

/--
info: 'ArrayDeque.toList_pushBack' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_pushBack

/--
info: 'ArrayDeque.toList_pushFront' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_pushFront

/--
info: 'ArrayDeque.popFront?_fst' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.popFront?_fst

/--
info: 'ArrayDeque.toList_popFront?_snd' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_popFront?_snd

/--
info: 'ArrayDeque.popBack?_fst' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.popBack?_fst

/--
info: 'ArrayDeque.toList_popBack?_snd' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_popBack?_snd

/--
info: 'ArrayDeque.toList_popFront' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_popFront

/--
info: 'ArrayDeque.toList_popBack' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_popBack

/--
info: 'ArrayDeque.toList_set' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_set

/--
info: 'ArrayDeque.toList_setIfInBounds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_setIfInBounds

/--
info: 'ArrayDeque.toList_ofList' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_ofList

/--
info: 'ArrayDeque.toList_empty' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_empty

/--
info: 'ArrayDeque.toList_emptyWithCapacity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toList_emptyWithCapacity

/--
info: 'ArrayDeque.length_toList' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.length_toList

/--
info: 'ArrayDeque.getElem_toList' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.getElem_toList

/--
info: 'ArrayDeque.getElem?_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.getElem?_eq

/--
info: 'ArrayDeque.front?_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.front?_eq

/--
info: 'ArrayDeque.back?_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.back?_eq

/--
info: 'ArrayDeque.isEmpty_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.isEmpty_eq

/--
info: 'ArrayDeque.foldl_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.foldl_eq

/--
info: 'ArrayDeque.forIn_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.forIn_eq

/--
info: 'ArrayDeque.getElem_eq_getElem_toList' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.getElem_eq_getElem_toList

/--
info: 'ArrayDeque.toArray_eq' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.toArray_eq

/--
info: 'ArrayDeque.getElem!_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArrayDeque.getElem!_eq
