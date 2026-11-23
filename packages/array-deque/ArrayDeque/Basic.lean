module

/-!
# ArrayDeque

A double-ended queue backed by a growable ring buffer over `Array`, in the style of Rust's
`VecDeque` and Java's `ArrayDeque`. Pushing and popping at either end take amortized O(1) time.

The capacity is always zero or a power of two, so logical indices map to physical ones with a bit
mask. Slots that hold no element contain `default`, which is why the operations that create or free
slots take `[Inhabited α]`. Freed slots are overwritten, so a popped element is not kept alive by
the deque.

## In-place updates

When the deque is not shared (reference count 1), every update modifies the buffer in place. Use the
deque linearly to keep it that way: after `let d' := d.pushBack x`, do not use `d` again.
`popFront?` and `popBack?` always return the deque, even when it is empty, so the natural
`let (x?, d') := d.popFront?` pattern never keeps the old deque alive.
-/

@[expose] public section

universe u v w

/--
A double-ended queue backed by a ring buffer.

The logical element `i` (for `i < size`) lives at physical index `(head + i) &&& (buf.size - 1)`.
The invariants are part of the structure, so every value of this type is well formed.
-/
structure ArrayDeque (α : Type u) where
  /-- The ring buffer. Its size is the capacity, which is zero or a power of two. -/
  buf : Array α
  /-- The physical index of the first element. -/
  head : Nat
  /-- The number of elements. -/
  size : Nat
  /-- The elements fit in the buffer. -/
  size_le : size ≤ buf.size
  /-- The capacity is zero or a power of two. -/
  cap_pow2 : buf.size = 0 ∨ buf.size.isPowerOfTwo
  /-- The head is a valid physical index (unless the buffer is empty). -/
  head_lt : head < buf.size ∨ buf.size = 0

namespace ArrayDeque

variable {α : Type u}

/-! ### Index arithmetic -/

/-- Internal. The physical index of logical index `i` in a ring buffer of capacity `cap` starting
at `head`. Only meaningful when `cap` is a power of two. -/
@[inline] def physIdx (head i cap : Nat) : Nat := (head + i) &&& (cap - 1)

theorem physIdx_lt {head i cap : Nat} (h : 0 < cap) : physIdx head i cap < cap := by
  have := @Nat.and_le_right (head + i) (cap - 1)
  unfold physIdx; omega

/-- Internal. The capacity used for a deque that must hold `n` elements: `0` for `n = 0`,
otherwise the next power of two. -/
def capFor (n : Nat) : Nat := if n = 0 then 0 else n.nextPowerOfTwo

theorem capFor_pow2 (n : Nat) : capFor n = 0 ∨ (capFor n).isPowerOfTwo := by
  unfold capFor; split
  · exact .inl rfl
  · exact .inr (Nat.isPowerOfTwo_nextPowerOfTwo n)

theorem le_capFor (n : Nat) : n ≤ capFor n := by
  unfold capFor; split
  · omega
  · exact Nat.le_nextPowerOfTwo n

/-- Internal. The capacity after growing a full buffer of capacity `c`. -/
def newCap (c : Nat) : Nat := if c = 0 then 4 else 2 * c

theorem newCap_pow2 {c : Nat} (h : c = 0 ∨ c.isPowerOfTwo) : (newCap c).isPowerOfTwo := by
  unfold newCap
  split
  · have h2 := Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo Nat.isPowerOfTwo_one
    simpa using Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo h2
  · rcases h with h | h
    · omega
    · rw [Nat.mul_comm]; exact Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo h

theorem lt_newCap (c : Nat) : c < newCap c := by unfold newCap; split <;> omega

/-! ### Construction and queries -/

/-- The empty deque. It has capacity 0 and does not allocate. -/
def empty : ArrayDeque α := ⟨#[], 0, 0, by simp, by simp, by simp⟩

instance : EmptyCollection (ArrayDeque α) := ⟨empty⟩

instance : Inhabited (ArrayDeque α) := ⟨empty⟩

/-- An empty deque with room for at least `n` elements before it has to grow. -/
def emptyWithCapacity [Inhabited α] (n : Nat) : ArrayDeque α :=
  ⟨Array.replicate (capFor n) default, 0, 0, by simp,
    by simpa using capFor_pow2 n,
    by simp only [Array.size_replicate]; omega⟩

/-- The number of elements the deque can hold before it has to grow. -/
def capacity (d : ArrayDeque α) : Nat := d.buf.size

/-- Whether the deque has no elements. -/
def isEmpty (d : ArrayDeque α) : Bool := d.size == 0

theorem buf_size_pos_of_lt {d : ArrayDeque α} {i : Nat} (h : i < d.size) : 0 < d.buf.size := by
  have := d.size_le; omega

/-- The element at logical index `i`. Usually written `d[i]`. -/
@[inline] def get (d : ArrayDeque α) (i : Nat) (h : i < d.size) : α :=
  d.buf[physIdx d.head i d.buf.size]'(physIdx_lt (buf_size_pos_of_lt h))

instance : GetElem (ArrayDeque α) Nat α (fun d i => i < d.size) where
  getElem d i h := d.get i h

instance : GetElem? (ArrayDeque α) Nat α (fun d i => i < d.size) where
  getElem? d i := if h : i < d.size then some (d.get i h) else none

instance : LawfulGetElem (ArrayDeque α) Nat α (fun d i => i < d.size) where

/-- The first element, if any. -/
def front? (d : ArrayDeque α) : Option α := d[0]?

/-- The last element, if any. -/
def back? (d : ArrayDeque α) : Option α := d[d.size - 1]?

/-! ### Updates -/

/-- Replaces the element at logical index `i`. -/
def set (d : ArrayDeque α) (i : Nat) (x : α) (h : i < d.size := by get_elem_tactic) :
    ArrayDeque α :=
  match d, h with
  | ⟨buf, head, size, h₁, h₂, h₃⟩, h =>
    let cap := buf.size
    have h0 : 0 < cap := by simp at h; omega
    let buf' := buf.set (physIdx head i cap) x (physIdx_lt h0)
    ⟨buf', head, size, by simpa [buf'] using h₁, by simpa [buf'] using h₂,
      by simpa [buf'] using h₃⟩

/-- Replaces the element at logical index `i`, or returns the deque unchanged if `i` is out of
bounds. -/
def setIfInBounds (d : ArrayDeque α) (i : Nat) (x : α) : ArrayDeque α :=
  if h : i < d.size then d.set i x h else d

/-- Internal. Moves the elements into a new buffer of twice the capacity (4 if the capacity is 0),
starting at physical index 0. Used by the push operations when the buffer is full. -/
def grow [Inhabited α] (d : ArrayDeque α) : ArrayDeque α :=
  ⟨Array.ofFn (n := newCap d.buf.size) fun i => if h : i.1 < d.size then d.get i h else default,
    0, d.size,
    by have := d.size_le; have := lt_newCap d.buf.size; simp only [Array.size_ofFn]; omega,
    by right; simpa using newCap_pow2 d.cap_pow2,
    by left; have := lt_newCap d.buf.size; simp only [Array.size_ofFn]; omega⟩

theorem size_grow [Inhabited α] (d : ArrayDeque α) : (grow d).size = d.size := rfl

theorem size_lt_capacity_grow [Inhabited α] (d : ArrayDeque α) :
    (grow d).size < (grow d).buf.size := by
  have := d.size_le; have := lt_newCap d.buf.size
  simp only [grow, Array.size_ofFn]; omega

/-- Internal. `pushBack` on a deque that is known not to be full. -/
@[inline] def pushBackCore (d : ArrayDeque α) (x : α) (hlt : d.size < d.buf.size) :
    ArrayDeque α :=
  match d, hlt with
  | ⟨buf, head, size, _, h₂, h₃⟩, hlt =>
    let cap := buf.size
    let j := physIdx head size cap
    have hj : j < cap := physIdx_lt (by simp at hlt; omega)
    let buf' := buf.set j x hj
    ⟨buf', head, size + 1, by simp only [buf', Array.size_set]; simp at hlt; omega,
      by simpa [buf'] using h₂, by simpa [buf'] using h₃⟩

/-- Adds an element at the back. Amortized O(1). -/
def pushBack [Inhabited α] (d : ArrayDeque α) (x : α) : ArrayDeque α :=
  if h : d.size < d.buf.size then pushBackCore d x h
  else pushBackCore (grow d) x (size_lt_capacity_grow d)

/-- Internal. `pushFront` on a deque that is known not to be full. -/
@[inline] def pushFrontCore (d : ArrayDeque α) (x : α) (hlt : d.size < d.buf.size) :
    ArrayDeque α :=
  match d, hlt with
  | ⟨buf, head, size, _, h₂, _⟩, hlt =>
    let cap := buf.size
    -- `+ cap` keeps the `Nat` subtraction from truncating at 0.
    let head' := (head + cap - 1) &&& (cap - 1)
    have hj : head' < cap := by
      have := @Nat.and_le_right (head + cap - 1) (cap - 1); simp at hlt; omega
    let buf' := buf.set head' x hj
    ⟨buf', head', size + 1, by simp only [buf', Array.size_set]; simp at hlt; omega,
      by simpa [buf'] using h₂, by left; simpa [buf'] using hj⟩

/-- Adds an element at the front. Amortized O(1). -/
def pushFront [Inhabited α] (d : ArrayDeque α) (x : α) : ArrayDeque α :=
  if h : d.size < d.buf.size then pushFrontCore d x h
  else pushFrontCore (grow d) x (size_lt_capacity_grow d)

/-- Removes the first element. Returns it (or `none` if the deque is empty) together with the
remaining deque, which is returned even when empty so that the old deque can be dropped:
`let (x?, d) := d.popFront?`. O(1). -/
def popFront? [Inhabited α] (d : ArrayDeque α) : Option α × ArrayDeque α :=
  match d with
  | ⟨buf, head, size, h₁, h₂, h₃⟩ =>
    if hs : size = 0 then (none, ⟨buf, head, size, h₁, h₂, h₃⟩)
    else
      -- Read everything we need from `buf` before `set`, so that `set` sees a unique array.
      let cap := buf.size
      let x := buf[head]'(by omega)
      let buf' := buf.set head default (by omega)
      (some x, ⟨buf', (head + 1) &&& (cap - 1), size - 1, by simp [buf']; omega,
        by simpa [buf'] using h₂,
        by
          left; simp only [buf', Array.size_set]
          have := @Nat.and_le_right (head + 1) (cap - 1); omega⟩)

/-- Removes the last element. Returns it (or `none` if the deque is empty) together with the
remaining deque, which is returned even when empty so that the old deque can be dropped:
`let (x?, d) := d.popBack?`. O(1). -/
def popBack? [Inhabited α] (d : ArrayDeque α) : Option α × ArrayDeque α :=
  match d with
  | ⟨buf, head, size, h₁, h₂, h₃⟩ =>
    if hs : size = 0 then (none, ⟨buf, head, size, h₁, h₂, h₃⟩)
    else
      let cap := buf.size
      let j := physIdx head (size - 1) cap
      have hj : j < cap := physIdx_lt (by omega)
      let x := buf[j]
      let buf' := buf.set j default hj
      (some x, ⟨buf', head, size - 1, by simp [buf']; omega,
        by simpa [buf'] using h₂, by simpa [buf'] using h₃⟩)

/-- Removes the first element, if any. -/
@[inline] def popFront [Inhabited α] (d : ArrayDeque α) : ArrayDeque α := d.popFront?.2

/-- Removes the last element, if any. -/
@[inline] def popBack [Inhabited α] (d : ArrayDeque α) : ArrayDeque α := d.popBack?.2

/-! ### Conversions and traversal -/

/-- The elements from front to back, as an array. O(n). -/
def toArray (d : ArrayDeque α) : Array α := Array.ofFn (n := d.size) fun i => d.get i i.2

/-- The elements from front to back, as a list. This is the abstract model of the deque. O(n). -/
def toList (d : ArrayDeque α) : List α := d.toArray.toList

/-- A deque with the elements of `l`, front to back. O(n). -/
def ofList [Inhabited α] (l : List α) : ArrayDeque α :=
  ⟨l.toArray ++ Array.replicate (capFor l.length - l.length) default, 0, l.length,
    by
      have := le_capFor l.length
      simp only [Array.size_append, List.size_toArray, Array.size_replicate]; omega,
    by
      have h := capFor_pow2 l.length; have := le_capFor l.length
      have e : l.length + (capFor l.length - l.length) = capFor l.length := by omega
      simp only [Array.size_append, List.size_toArray, Array.size_replicate, e]; exact h,
    by
      have := le_capFor l.length
      simp only [Array.size_append, List.size_toArray, Array.size_replicate]; omega⟩

/-- Internal. The loop behind `foldl`, starting at logical index `i`. -/
@[specialize] def foldlLoop {β : Type v} (f : β → α → β) (d : ArrayDeque α) (i : Nat) (b : β) :
    β :=
  if h : i < d.size then foldlLoop f d (i + 1) (f b (d.get i h)) else b
termination_by d.size - i

/-- Folds `f` over the elements from front to back. -/
@[inline] def foldl {β : Type v} (f : β → α → β) (init : β) (d : ArrayDeque α) : β :=
  foldlLoop f d 0 init

/-- Internal. The loop behind the `ForIn` instance, starting at logical index `i`. -/
@[specialize] def forInLoop {m : Type v → Type w} [Monad m] {β : Type v} (d : ArrayDeque α)
    (f : α → β → m (ForInStep β)) (i : Nat) (b : β) : m β :=
  if h : i < d.size then do
    match ← f (d.get i h) b with
    | .done b => pure b
    | .yield b => forInLoop d f (i + 1) b
  else pure b
termination_by d.size - i

instance {m : Type v → Type w} [Monad m] : ForIn m (ArrayDeque α) α where
  forIn d b f := forInLoop d f 0 b

instance [Repr α] : Repr (ArrayDeque α) where
  reprPrec d prec := Repr.addAppParen ("ArrayDeque.ofList " ++ repr d.toList) prec

end ArrayDeque

end
