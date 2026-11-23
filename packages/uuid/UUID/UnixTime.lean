module

public import UUID.Random
public import Std.Time

/-!
# Time-ordered UUIDs (version 7)

A version 7 UUID (RFC 9562 §5.7) starts with a 48-bit big-endian Unix timestamp in milliseconds,
followed by 74 random bits:

```
| unix_ts_ms (48) | ver (4) | rand_a (12) | var (2) | rand_b (62) |
```

Because the timestamp comes first, v7 UUIDs generated later sort after earlier ones, which makes
them good database keys.

* `UUID.v7` generates a v7 UUID from the current time and fresh randomness.
* `UUID.V7Generator` additionally guarantees that the UUIDs it returns are *strictly increasing*,
  even when several are generated within the same millisecond or the clock goes backwards
  (RFC 9562 §6.2).
-/

@[expose] public section

namespace UUID

/-! ## Construction -/

/--
The version 7 UUID with the given timestamp and random fields. Only the low 48 bits of `unixMs`,
the low 12 bits of `randA` and the low 62 bits of `randB` are used.
This is the pure core of `UUID.v7`.
-/
def v7Of (unixMs : UInt64) (randA : UInt16) (randB : UInt64) : UUID :=
  (UUID.mk ((unixMs <<< 16) ||| (randA.toUInt64 &&& 0xFFF)) randB).withVersion .unixTime

/-- The Unix timestamp (milliseconds) of a version 7 UUID, or `none` for other versions. -/
def unixTimeMs? (u : UUID) : Option UInt64 :=
  if u.version? = some .unixTime then some (u.hi >>> 16) else none

@[simp] theorem version?_v7Of (unixMs : UInt64) (randA : UInt16) (randB : UInt64) :
    (v7Of unixMs randA randB).version? = some .unixTime := by
  simp [v7Of]

@[simp] theorem unixTimeMs?_v7Of (unixMs : UInt64) (randA : UInt16) (randB : UInt64) :
    (v7Of unixMs randA randB).unixTimeMs? = some (unixMs &&& 0xFFFFFFFFFFFF) := by
  simp only [unixTimeMs?, version?_v7Of, ↓reduceIte, Option.some.injEq]
  simp only [v7Of, withVersion, Version.toUInt8]
  bv_decide

/-! ## Current time -/

/-- Milliseconds since the Unix epoch, according to the system clock. -/
def unixTimeMsNow : IO UInt64 := do
  let now ← Std.Time.Timestamp.now
  return now.toMillisecondsSinceUnixEpoch.toInt.toNat.toUInt64

/-- Generate a version 7 UUID from the current time and fresh random bits.

UUIDs generated in the same millisecond are not ordered among themselves; use `V7Generator` if
you need strictly increasing UUIDs. -/
def v7 : IO UUID := do
  let ms ← unixTimeMsNow
  let r ← randomBits
  return v7Of ms r.hi.toUInt16 r.lo

/-! ## Monotonic generation -/

namespace V7

/--
The next v7 UUID after `u` in the same "timestamp + counter" order: the 74 bits
`rand_a ++ rand_b` are treated as a counter and incremented, carrying into the timestamp on
overflow. The version and variant bits are preserved.
-/
def succ (u : UUID) : UUID :=
  if u.lo &&& 0x3FFFFFFFFFFFFFFF < 0x3FFFFFFFFFFFFFFF then
    ⟨u.hi, u.lo + 1⟩
  else
    let lo := u.lo &&& 0xC000000000000000
    if u.hi &&& 0xFFF < 0xFFF then
      ⟨u.hi + 1, lo⟩
    else
      ⟨(((u.hi >>> 16) + 1) <<< 16) ||| (u.hi &&& 0xF000), lo⟩

/--
The pure core of `V7Generator.next`: given the previously issued UUID `last`, the current time
and fresh random fields, return a UUID strictly greater than `last` (unless the 48-bit timestamp
has overflowed, around the year 10889).

If the freshly built UUID already sorts after `last` it is used as is; otherwise (same
millisecond with smaller random bits, or the clock went backwards) `last` is incremented.
-/
def next (last : UUID) (unixMs : UInt64) (randA : UInt16) (randB : UInt64) : UUID :=
  let fresh := v7Of unixMs randA randB
  if last < fresh then fresh else succ last

/-- `succ` is strictly increasing, as long as the timestamp of `u` is not already the largest
48-bit value. -/
theorem lt_succ (u : UUID) (h : u.hi >>> 16 < 0xFFFFFFFFFFFF) : u < succ u := by
  rw [lt_iff]
  unfold succ
  split
  · bv_decide
  · split <;> bv_decide

/-- **Monotonicity.** `next` always returns a UUID strictly greater than the previous one
(barring timestamp overflow in the year 10889). -/
theorem lt_next (last : UUID) (unixMs : UInt64) (randA : UInt16) (randB : UInt64)
    (h : last.hi >>> 16 < 0xFFFFFFFFFFFF) : last < next last unixMs randA randB := by
  dsimp only [next]
  split
  · assumption
  · exact lt_succ last h

/-- `succ` preserves the version field. -/
theorem versionNumber_succ (u : UUID) : (succ u).versionNumber = u.versionNumber := by
  unfold succ versionNumber
  split
  · rfl
  · split <;> bv_decide

/-- `succ` preserves the RFC 9562 variant. -/
theorem variant_succ (u : UUID) (h : u.variant = .rfc9562) : (succ u).variant = .rfc9562 := by
  rw [variant_eq_rfc9562_iff] at *
  unfold succ
  split
  · bv_decide
  · split <;> bv_decide

/-- `succ` maps RFC 9562 UUIDs to RFC 9562 UUIDs of the same version. -/
theorem version?_succ (u : UUID) (h : u.variant = .rfc9562) :
    (succ u).version? = u.version? := by
  unfold version?
  rw [variant_succ u h, versionNumber_succ, h]

end V7

/-- A generator of strictly increasing version 7 UUIDs (RFC 9562 §6.2). -/
structure V7Generator where
  /-- The most recently issued UUID (`UUID.nil` initially). -/
  last : IO.Ref UUID

namespace V7Generator

/-- Create a new generator. -/
def new : BaseIO V7Generator :=
  V7Generator.mk <$> IO.mkRef nil

/-- Generate a version 7 UUID that is strictly greater than every UUID previously returned by
this generator. -/
def next (g : V7Generator) : IO UUID := do
  let ms ← unixTimeMsNow
  let r ← randomBits
  g.last.modifyGet fun last =>
    let u := V7.next last ms r.hi.toUInt16 r.lo
    (u, u)

end V7Generator

end UUID

end
