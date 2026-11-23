module

-- `Nat.isPowerOfTwo` has no exposed body, so we need `import all` to unfold it to `∃ k, n = 2 ^ k`.
-- This import is private: downstream modules still cannot see the body.
import all Init.Data.Nat.Power2.Basic

public import ArrayDeque.Basic

/-!
# Specification of `ArrayDeque`

Every operation is characterized by its effect on the abstract model `toList`.
-/

@[expose] public section

namespace ArrayDeque

universe u v w

variable {α : Type u}

/-! ### Index arithmetic -/

theorem physIdx_eq_mod {head i cap : Nat} (hp : cap.isPowerOfTwo) :
    physIdx head i cap = (head + i) % cap := by
  obtain ⟨k, rfl⟩ := hp
  unfold physIdx
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem physIdx_eq {head i cap : Nat} (hp : cap.isPowerOfTwo) (hh : head < cap) (hi : i < cap) :
    physIdx head i cap = if head + i < cap then head + i else head + i - cap := by
  rw [physIdx_eq_mod hp]
  split
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem physIdx_zero {head cap : Nat} (hp : cap.isPowerOfTwo) (hh : head < cap) :
    physIdx head 0 cap = head := by
  rw [physIdx_eq_mod hp, Nat.add_zero, Nat.mod_eq_of_lt hh]

theorem physIdx_inj {head i j cap : Nat} (hp : cap.isPowerOfTwo) (hh : head < cap)
    (hi : i < cap) (hj : j < cap) (e : physIdx head i cap = physIdx head j cap) : i = j := by
  rw [physIdx_eq hp hh hi, physIdx_eq hp hh hj] at e
  split at e <;> split at e <;> omega

theorem physIdx_physIdx {head a b cap : Nat} (hp : cap.isPowerOfTwo) :
    physIdx (physIdx head a cap) b cap = physIdx head (a + b) cap := by
  rw [physIdx_eq_mod hp, physIdx_eq_mod hp, physIdx_eq_mod hp, Nat.mod_add_mod, Nat.add_assoc]

/-! ### The model -/

@[simp] theorem length_toList (d : ArrayDeque α) : d.toList.length = d.size := by
  simp [toList, toArray]

theorem getElem_toList_eq_get (d : ArrayDeque α) (i : Nat) (h : i < d.toList.length) :
    d.toList[i] = d.get i (by simpa using h) := by
  simp [toList, toArray]

/-- Not a simp lemma: the simp normal form goes the other way (`getElem_eq_getElem_toList`). -/
theorem getElem_toList (d : ArrayDeque α) (i : Nat) (h : i < d.toList.length) :
    d.toList[i] = d[i]'(by simpa using h) :=
  getElem_toList_eq_get d i h

/-- The simp normal form of indexing is indexing into the model `toList`, where the `toList_*`
lemmas of each operation apply. -/
@[simp] theorem getElem_eq_getElem_toList (d : ArrayDeque α) (i : Nat) (h : i < d.size) :
    d[i] = d.toList[i]'(by simpa using h) :=
  (getElem_toList d i (by simpa using h)).symm

@[simp] theorem toList_eq_nil_iff (d : ArrayDeque α) : d.toList = [] ↔ d.size = 0 := by
  rw [← List.length_eq_zero_iff, length_toList]

@[simp] theorem toList_toArray (d : ArrayDeque α) : d.toArray.toList = d.toList := rfl

@[simp] theorem size_toArray (d : ArrayDeque α) : d.toArray.size = d.size := by
  simp [toArray]

@[simp] theorem toArray_eq (d : ArrayDeque α) : d.toArray = d.toList.toArray := by
  rw [← toList_toArray]

theorem getElem_toArray (d : ArrayDeque α) (i : Nat) (h : i < d.toArray.size) :
    d.toArray[i] = d.toList[i]'(by simpa using h) := by
  simp only [toArray_eq, List.getElem_toArray]

@[simp] theorem getElem?_eq (d : ArrayDeque α) (i : Nat) : d[i]? = d.toList[i]? := by
  show (if h : i < d.size then some (d.get i h) else none) = _
  split
  · next h => rw [List.getElem?_eq_getElem (by simpa using h), getElem_toList]; rfl
  · next h => rw [List.getElem?_eq_none (by simp; omega)]

@[simp] theorem getElem!_eq [Inhabited α] (d : ArrayDeque α) (i : Nat) :
    d[i]! = d.toList[i]! := by
  simp [getElem!_def]

/-! ### Invariants -/

theorem size_le_capacity (d : ArrayDeque α) : d.size ≤ d.capacity := d.size_le

theorem capacity_eq_zero_or_isPowerOfTwo (d : ArrayDeque α) :
    d.capacity = 0 ∨ d.capacity.isPowerOfTwo := d.cap_pow2

/-! ### Construction and queries -/

@[simp] theorem toList_empty : (∅ : ArrayDeque α).toList = [] :=
  (toList_eq_nil_iff _).2 rfl

@[simp] theorem toList_emptyWithCapacity [Inhabited α] {n : Nat} :
    (emptyWithCapacity n : ArrayDeque α).toList = [] :=
  (toList_eq_nil_iff _).2 rfl

theorem le_capacity_emptyWithCapacity [Inhabited α] (n : Nat) :
    n ≤ (emptyWithCapacity n : ArrayDeque α).capacity := by
  simpa [emptyWithCapacity, capacity] using le_capFor n

@[simp] theorem isEmpty_eq (d : ArrayDeque α) : d.isEmpty = d.toList.isEmpty := by
  rw [isEmpty, Bool.eq_iff_iff, beq_iff_eq, List.isEmpty_iff, toList_eq_nil_iff]

@[simp] theorem front?_eq (d : ArrayDeque α) : d.front? = d.toList.head? := by
  unfold front?; rw [getElem?_eq, List.head?_eq_getElem?]

@[simp] theorem back?_eq (d : ArrayDeque α) : d.back? = d.toList.getLast? := by
  unfold back?; rw [getElem?_eq, List.getLast?_eq_getElem?, length_toList]

/-! ### Updates -/

@[simp] theorem toList_set (d : ArrayDeque α) (i : Nat) (x : α) (h : i < d.size) :
    (d.set i x h).toList = d.toList.set i x := by
  obtain ⟨buf, head, size, h₁, h₂, h₃⟩ := d
  simp only at h
  have hp : buf.size.isPowerOfTwo := h₂.resolve_left (by omega)
  have hh : head < buf.size := by omega
  apply List.ext_getElem
  · simp [set]
  · intro j h1 h2
    simp only [length_toList, set] at h1
    simp only [getElem_toList_eq_get, get, set, Array.getElem_set, List.getElem_set,
      Array.size_set]
    by_cases e : i = j
    · subst e; simp
    · rw [ite_eq_right (fun e' => absurd (physIdx_inj hp hh (by omega) (by omega) e') e),
        ite_eq_right (fun e' => absurd e' e)]

@[simp] theorem toList_setIfInBounds (d : ArrayDeque α) (i : Nat) (x : α) :
    (d.setIfInBounds i x).toList = d.toList.set i x := by
  unfold setIfInBounds
  split
  · exact toList_set ..
  · rw [List.set_eq_of_length_le (by simp; omega)]

theorem toList_grow [Inhabited α] (d : ArrayDeque α) : (grow d).toList = d.toList := by
  apply List.ext_getElem
  · simp [size_grow]
  · intro i h1 h2
    simp only [length_toList, size_grow] at h1
    have hidx : physIdx (grow d).head i (grow d).buf.size = i := by
      have := lt_newCap d.buf.size
      have := d.size_le
      obtain ⟨k, hk⟩ := newCap_pow2 d.cap_pow2
      unfold physIdx
      simp only [grow, Array.size_ofFn, hk, Nat.zero_add, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_eq_of_lt (by simp only [grow] at *; omega)
    simp only [getElem_toList_eq_get, get]
    simp only [hidx]
    simp only [grow, Array.getElem_ofFn, h1, ↓reduceDIte, get]

theorem toList_pushBackCore (d : ArrayDeque α) (x : α) (h : d.size < d.buf.size) :
    (d.pushBackCore x h).toList = d.toList ++ [x] := by
  obtain ⟨buf, head, size, h₁, h₂, h₃⟩ := d
  simp only at h
  have hp : buf.size.isPowerOfTwo := h₂.resolve_left (by omega)
  have hh : head < buf.size := by omega
  apply List.ext_getElem
  · simp [pushBackCore]
  · intro i h1 h2
    simp only [length_toList, pushBackCore] at h1
    rw [List.getElem_append]
    simp only [getElem_toList_eq_get, get, pushBackCore, Array.getElem_set, Array.size_set,
      length_toList]
    by_cases hi : i < size
    · rw [dite_eq_left hi, ite_eq_right]
      intro e
      have := physIdx_inj hp hh (by omega) (by omega) e
      omega
    · have : i = size := by omega
      subst this
      simp

@[simp] theorem toList_pushBack [Inhabited α] (d : ArrayDeque α) (x : α) :
    (d.pushBack x).toList = d.toList ++ [x] := by
  unfold pushBack
  split
  · exact toList_pushBackCore ..
  · rw [toList_pushBackCore, toList_grow]

theorem toList_pushFrontCore (d : ArrayDeque α) (x : α) (h : d.size < d.buf.size) :
    (d.pushFrontCore x h).toList = x :: d.toList := by
  obtain ⟨buf, head, size, h₁, h₂, h₃⟩ := d
  simp only at h
  have hp : buf.size.isPowerOfTwo := h₂.resolve_left (by omega)
  have hh : head < buf.size := by omega
  have hh' : (head + buf.size - 1) &&& (buf.size - 1) = physIdx head (buf.size - 1) buf.size := by
    unfold physIdx; congr 1; omega
  apply List.ext_getElem
  · simp [pushFrontCore]
  · intro i h1 h2
    simp only [length_toList, pushFrontCore] at h1
    simp only [getElem_toList_eq_get, get, pushFrontCore, Array.getElem_set, Array.size_set]
    simp only [hh', physIdx_physIdx hp]
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getElem_cons_succ, getElem_toList_eq_get, get]
      have e : physIdx head (buf.size - 1 + (i + 1)) buf.size = physIdx head i buf.size := by
        rw [physIdx_eq_mod hp, physIdx_eq_mod hp,
          show head + (buf.size - 1 + (i + 1)) = head + i + buf.size by omega, Nat.add_mod_right]
      simp only [e]
      rw [ite_eq_right]
      intro e'
      have := physIdx_inj hp hh (by omega) (by omega) e'
      omega

@[simp] theorem toList_pushFront [Inhabited α] (d : ArrayDeque α) (x : α) :
    (d.pushFront x).toList = x :: d.toList := by
  unfold pushFront
  split
  · exact toList_pushFrontCore ..
  · rw [toList_pushFrontCore, toList_grow]

theorem toList_of_size_zero {buf : Array α} {head : Nat} {h₁ h₂ h₃} :
    (⟨buf, head, 0, h₁, h₂, h₃⟩ : ArrayDeque α).toList = [] :=
  (toList_eq_nil_iff _).2 rfl

@[simp] theorem popFront?_fst [Inhabited α] (d : ArrayDeque α) :
    d.popFront?.1 = d.toList.head? := by
  obtain ⟨buf, head, size, h₁, h₂, h₃⟩ := d
  by_cases hs : size = 0
  · subst hs
    simp [popFront?, toList_of_size_zero]
  · have hp : buf.size.isPowerOfTwo := h₂.resolve_left (by omega)
    have hh : head < buf.size := by omega
    have hne : (⟨buf, head, size, h₁, h₂, h₃⟩ : ArrayDeque α).toList ≠ [] := by
      rw [ne_eq, toList_eq_nil_iff]; exact hs
    rw [List.head?_eq_some_head hne]
    simp only [popFront?, hs, ↓reduceDIte, Option.some.injEq]
    rw [List.head_eq_getElem]; simp only [getElem_toList_eq_get, get]
    congr 1; rw [physIdx_zero hp hh]

@[simp] theorem toList_popFront?_snd [Inhabited α] (d : ArrayDeque α) :
    d.popFront?.2.toList = d.toList.tail := by
  obtain ⟨buf, head, size, h₁, h₂, h₃⟩ := d
  by_cases hs : size = 0
  · subst hs
    simp [popFront?, toList_of_size_zero]
  · have hp : buf.size.isPowerOfTwo := h₂.resolve_left (by omega)
    have hh : head < buf.size := by omega
    simp only [popFront?, hs, ↓reduceDIte]
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [length_toList] at h1
      simp only [getElem_toList_eq_get, List.getElem_tail, get, Array.getElem_set,
        Array.size_set]
      have e1 : (head + 1) &&& (buf.size - 1) = physIdx head 1 buf.size := rfl
      simp only [e1, physIdx_physIdx hp, Nat.add_comm 1 i]
      rw [ite_eq_right]
      intro e'
      have := physIdx_inj (i := 0) (j := i + 1) hp hh (by omega) (by omega)
        ((physIdx_zero hp hh).trans e')
      omega

@[simp] theorem popBack?_fst [Inhabited α] (d : ArrayDeque α) :
    d.popBack?.1 = d.toList.getLast? := by
  obtain ⟨buf, head, size, h₁, h₂, h₃⟩ := d
  by_cases hs : size = 0
  · subst hs
    simp [popBack?, toList_of_size_zero]
  · have hne : (⟨buf, head, size, h₁, h₂, h₃⟩ : ArrayDeque α).toList ≠ [] := by
      rw [ne_eq, toList_eq_nil_iff]; exact hs
    rw [List.getLast?_eq_some_getLast hne]
    simp only [popBack?, hs, ↓reduceDIte, Option.some.injEq]
    rw [List.getLast_eq_getElem, getElem_toList_eq_get]; simp only [length_toList, get]

@[simp] theorem toList_popBack?_snd [Inhabited α] (d : ArrayDeque α) :
    d.popBack?.2.toList = d.toList.dropLast := by
  obtain ⟨buf, head, size, h₁, h₂, h₃⟩ := d
  by_cases hs : size = 0
  · subst hs
    simp [popBack?, toList_of_size_zero]
  · have hp : buf.size.isPowerOfTwo := h₂.resolve_left (by omega)
    have hh : head < buf.size := by omega
    simp only [popBack?, hs, ↓reduceDIte]
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [length_toList] at h1
      simp only [getElem_toList_eq_get, List.getElem_dropLast, get, Array.getElem_set,
        Array.size_set]
      rw [ite_eq_right]
      intro e'
      have := physIdx_inj hp hh (by omega) (by omega) e'
      omega

@[simp] theorem toList_popFront [Inhabited α] (d : ArrayDeque α) :
    d.popFront.toList = d.toList.tail :=
  toList_popFront?_snd d

@[simp] theorem toList_popBack [Inhabited α] (d : ArrayDeque α) :
    d.popBack.toList = d.toList.dropLast :=
  toList_popBack?_snd d

/-! ### Sizes -/

@[simp] theorem size_pushBack [Inhabited α] (d : ArrayDeque α) (x : α) :
    (d.pushBack x).size = d.size + 1 := by
  rw [← length_toList, toList_pushBack]; simp

@[simp] theorem size_pushFront [Inhabited α] (d : ArrayDeque α) (x : α) :
    (d.pushFront x).size = d.size + 1 := by
  rw [← length_toList, toList_pushFront]; simp

@[simp] theorem size_popFront?_snd [Inhabited α] (d : ArrayDeque α) :
    d.popFront?.2.size = d.size - 1 := by
  rw [← length_toList, toList_popFront?_snd]; simp

@[simp] theorem size_popBack?_snd [Inhabited α] (d : ArrayDeque α) :
    d.popBack?.2.size = d.size - 1 := by
  rw [← length_toList, toList_popBack?_snd]; simp

@[simp] theorem size_popFront [Inhabited α] (d : ArrayDeque α) :
    d.popFront.size = d.size - 1 := size_popFront?_snd d

@[simp] theorem size_popBack [Inhabited α] (d : ArrayDeque α) :
    d.popBack.size = d.size - 1 := size_popBack?_snd d

@[simp] theorem size_set (d : ArrayDeque α) (i : Nat) (x : α) (h : i < d.size) :
    (d.set i x h).size = d.size := by
  rw [← length_toList, toList_set]; simp

@[simp] theorem size_setIfInBounds (d : ArrayDeque α) (i : Nat) (x : α) :
    (d.setIfInBounds i x).size = d.size := by
  rw [← length_toList, toList_setIfInBounds]; simp

/-! ### Conversions and traversal -/

@[simp] theorem toList_ofList [Inhabited α] (l : List α) : (ofList l).toList = l := by
  apply List.ext_getElem
  · simp [ofList]
  · intro i h1 h2
    simp only [length_toList, ofList] at h1
    simp only [getElem_toList_eq_get, get, ofList]
    have hc := capFor_pow2 l.length
    have := le_capFor l.length
    have hp : (capFor l.length).isPowerOfTwo := hc.resolve_left (by omega)
    have e : physIdx 0 i (l.toArray ++ Array.replicate (capFor l.length - l.length)
        (default : α)).size = i := by
      simp only [Array.size_append, List.size_toArray, Array.size_replicate,
        show l.length + (capFor l.length - l.length) = capFor l.length by omega]
      rw [physIdx_eq_mod hp, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    simp only [e]
    rw [Array.getElem_append_left (by simpa using h1)]
    simp

@[simp] theorem size_ofList [Inhabited α] (l : List α) : (ofList l).size = l.length := by
  rw [← length_toList, toList_ofList]

theorem foldlLoop_eq {β : Type v} (f : β → α → β) (d : ArrayDeque α) (i : Nat) (b : β) :
    foldlLoop f d i b = (d.toList.drop i).foldl f b := by
  fun_induction foldlLoop f d i b with
  | case1 i b h ih =>
    rw [List.drop_eq_getElem_cons (by simpa using h)]
    simp only [ih, List.foldl_cons, getElem_toList_eq_get]
  | case2 i b h =>
    rw [List.drop_eq_nil_of_le (by simp; omega)]; simp

@[simp] theorem foldl_eq {β : Type v} (f : β → α → β) (init : β) (d : ArrayDeque α) :
    d.foldl f init = d.toList.foldl f init := by
  unfold foldl; rw [foldlLoop_eq]; simp

theorem forInLoop_eq {m : Type v → Type w} [Monad m] [LawfulMonad m] {β : Type v}
    (d : ArrayDeque α) (f : α → β → m (ForInStep β)) (i : Nat) (b : β) :
    forInLoop d f i b = forIn (d.toList.drop i) b f := by
  fun_induction forInLoop d f i b with
  | case1 i b h ih =>
    rw [List.drop_eq_getElem_cons (by simpa using h)]
    simp only [List.forIn_cons, getElem_toList]
    congr 1; funext r; cases r <;> simp [ih]
  | case2 i b h =>
    rw [List.drop_eq_nil_of_le (by simp; omega)]; simp

@[simp] theorem forIn_eq {m : Type v → Type w} [Monad m] [LawfulMonad m] {β : Type v}
    (d : ArrayDeque α) (b : β) (f : α → β → m (ForInStep β)) :
    forIn d b f = forIn d.toList b f := by
  show forInLoop d f 0 b = _
  rw [forInLoop_eq]; simp

end ArrayDeque

end
