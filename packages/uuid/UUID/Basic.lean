module

public import Std.Tactic.BVDecide

/-!
# The `UUID` type

This module defines the core `UUID` type together with the variant and version fields described
in [RFC 9562](https://www.rfc-editor.org/rfc/rfc9562).

A UUID is a 128-bit value. We store it as two `UInt64` words in *network (big-endian) byte order*:
`hi` holds octets 0–7 and `lo` holds octets 8–15. With this layout

* the lexicographic `Ord` instance on `(hi, lo)` agrees with the RFC's ordering by unsigned
  octets, and
* the version and variant fields live at fixed bit positions, which makes them easy to reason
  about with `bv_decide`.

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                              hi                               |
+                               +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                               |  ver  |                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|var|                          lo                               |
+-+-+                                                           +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```
-/

@[expose] public section

/-- A 128-bit universally unique identifier, stored as two big-endian 64-bit words. -/
structure UUID where
  /-- Octets 0–7 (the most significant half). -/
  hi : UInt64
  /-- Octets 8–15 (the least significant half). -/
  lo : UInt64
deriving DecidableEq, Hashable

namespace UUID

/-! ## Ordering -/

/-- UUIDs are ordered as 128-bit unsigned integers, i.e. lexicographically by octet
(RFC 9562 §6.11). -/
instance : Ord UUID where
  compare u v := (compare u.hi v.hi).then (compare u.lo v.lo)

instance : LT UUID := ltOfOrd
instance : LE UUID := leOfOrd
instance : Max UUID := maxOfLe
instance : Min UUID := minOfLe

theorem compare_def (u v : UUID) :
    compare u v = (compare u.hi v.hi).then (compare u.lo v.lo) := rfl

theorem lt_iff (u v : UUID) : u < v ↔ u.hi < v.hi ∨ (u.hi = v.hi ∧ u.lo < v.lo) := by
  show compare u v = .lt ↔ _
  simp [compare_def, Ordering.then_eq_lt, Std.compare_eq_lt]

/-! ## Special values -/

/-- The Nil UUID `00000000-0000-0000-0000-000000000000` (RFC 9562 §5.9). -/
def nil : UUID := ⟨0, 0⟩

/-- The Max UUID `ffffffff-ffff-ffff-ffff-ffffffffffff` (RFC 9562 §5.10). -/
def max : UUID := ⟨0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF⟩

instance : Inhabited UUID := ⟨nil⟩

/-- Is this the Nil UUID? -/
def isNil (u : UUID) : Bool := u == nil

/-- Is this the Max UUID? -/
def isMax (u : UUID) : Bool := u == max

/-! ## Variant -/

/-- The variant field (RFC 9562 §4.1), which determines the layout of the rest of the UUID. -/
inductive Variant where
  /-- `0xxx`: reserved, NCS backward compatibility. Also covers the Nil UUID. -/
  | ncs
  /-- `10xx`: the variant specified by RFC 9562 (and RFC 4122 before it). -/
  | rfc9562
  /-- `110x`: reserved, Microsoft Corporation backward compatibility. -/
  | microsoft
  /-- `111x`: reserved for future definition. Also covers the Max UUID. -/
  | future
deriving Repr, DecidableEq, Inhabited, Hashable

/-- The variant of a UUID, read from the most significant bits of octet 8. -/
def variant (u : UUID) : Variant :=
  let b := (u.lo >>> 61).toUInt8
  if b < 4 then .ncs
  else if b < 6 then .rfc9562
  else if b = 6 then .microsoft
  else .future

theorem variant_eq_rfc9562_iff (u : UUID) : u.variant = .rfc9562 ↔ u.lo >>> 62 = 2 := by
  dsimp only [variant]
  split
  · simp only [reduceCtorEq, false_iff]; bv_decide
  · split
    · simp only [true_iff]; bv_decide
    · split <;> (simp only [reduceCtorEq, false_iff]; bv_decide)

/-! ## Version -/

/-- The UUID versions defined by RFC 9562 §4.2. -/
inductive Version where
  /-- Version 1: Gregorian time-based. -/
  | gregorian
  /-- Version 2: DCE Security. -/
  | dceSecurity
  /-- Version 3: name-based, using MD5. -/
  | md5
  /-- Version 4: randomly generated. -/
  | random
  /-- Version 5: name-based, using SHA-1. -/
  | sha1
  /-- Version 6: reordered Gregorian time-based. -/
  | reorderedGregorian
  /-- Version 7: Unix epoch time-based. -/
  | unixTime
  /-- Version 8: custom, vendor-specific layout. -/
  | custom
deriving Repr, DecidableEq, Inhabited, Hashable

namespace Version

/-- The 4-bit version number of a `Version` (`1`–`8`). -/
def toUInt8 : Version → UInt8
  | .gregorian => 1
  | .dceSecurity => 2
  | .md5 => 3
  | .random => 4
  | .sha1 => 5
  | .reorderedGregorian => 6
  | .unixTime => 7
  | .custom => 8

/-- Decode a 4-bit version number. Returns `none` for numbers that RFC 9562 does not define. -/
def ofUInt8? : UInt8 → Option Version
  | 1 => some .gregorian
  | 2 => some .dceSecurity
  | 3 => some .md5
  | 4 => some .random
  | 5 => some .sha1
  | 6 => some .reorderedGregorian
  | 7 => some .unixTime
  | 8 => some .custom
  | _ => none

theorem ofUInt8?_toUInt8 (v : Version) : ofUInt8? v.toUInt8 = some v := by
  cases v <;> rfl

theorem toUInt8_lt_16 (v : Version) : v.toUInt8 < 16 := by
  cases v <;> decide

end Version

/-- The raw 4-bit version field (the high nibble of octet 6), whatever the variant. -/
def versionNumber (u : UUID) : UInt8 :=
  ((u.hi >>> 12) &&& 0xF).toUInt8

/--
The version of an RFC 9562 UUID.

Returns `none` if the UUID does not use the RFC 9562 variant (for example the Nil and Max UUIDs)
or if its version number is not one that RFC 9562 defines.
-/
def version? (u : UUID) : Option Version :=
  if u.variant = .rfc9562 then Version.ofUInt8? u.versionNumber else none

/--
Overwrite the version and variant fields, turning 122 arbitrary bits into an RFC 9562 UUID of
version `v`. All other bits are kept unchanged.
-/
def withVersion (u : UUID) (v : Version) : UUID where
  hi := (u.hi &&& (0xFFFFFFFFFFFF0FFF : UInt64)) ||| (v.toUInt8.toUInt64 <<< 12)
  lo := (u.lo &&& 0x3FFFFFFFFFFFFFFF) ||| 0x8000000000000000

theorem versionNumber_withVersion (u : UUID) (v : Version) :
    (u.withVersion v).versionNumber = v.toUInt8 := by
  have h := v.toUInt8_lt_16
  simp only [versionNumber, withVersion]
  generalize v.toUInt8 = x at *
  bv_decide

theorem variant_withVersion (u : UUID) (v : Version) :
    (u.withVersion v).variant = .rfc9562 := by
  have h₁ : ¬ ((u.withVersion v).lo >>> 61).toUInt8 < 4 := by
    simp only [withVersion]; bv_decide
  have h₂ : ((u.withVersion v).lo >>> 61).toUInt8 < 6 := by
    simp only [withVersion]; bv_decide
  simp [variant, h₁, h₂]

@[simp] theorem version?_withVersion (u : UUID) (v : Version) :
    (u.withVersion v).version? = some v := by
  simp [version?, variant_withVersion, versionNumber_withVersion, Version.ofUInt8?_toUInt8]

/-- `withVersion` only touches the version and variant bits, so applying it twice is the same as
applying the last one. -/
@[simp] theorem withVersion_withVersion (u : UUID) (v w : Version) :
    (u.withVersion v).withVersion w = u.withVersion w := by
  have h := v.toUInt8_lt_16
  simp only [withVersion, mk.injEq]
  generalize v.toUInt8 = x at *
  generalize w.toUInt8 = y
  constructor <;> bv_decide

/-! ## Version 8 -/

/--
A version 8 UUID (RFC 9562 §5.8) carrying 122 bits of application-defined data.

The version and variant bits of `custom` are overwritten; every other bit is kept.
-/
def v8Of (custom : UUID) : UUID := custom.withVersion .custom

end UUID

end
