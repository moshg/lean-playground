module

public import UUID.Basic

/-!
# Conversions between `UUID` and other representations

* `Vector UInt8 16` / `ByteArray`: the 16 octets in network byte order (RFC 9562 §4).
* `BitVec 128` / `Nat`: the UUID as a single 128-bit unsigned integer.

The round-trip properties are proved with `bv_decide`.
-/

@[expose] public section

namespace UUID

/-! ## Octets -/

/-- The 16 octets of a UUID in network byte order. -/
def toBytes (u : UUID) : Vector UInt8 16 :=
  #v[(u.hi >>> 56).toUInt8, (u.hi >>> 48).toUInt8, (u.hi >>> 40).toUInt8, (u.hi >>> 32).toUInt8,
     (u.hi >>> 24).toUInt8, (u.hi >>> 16).toUInt8, (u.hi >>> 8).toUInt8, u.hi.toUInt8,
     (u.lo >>> 56).toUInt8, (u.lo >>> 48).toUInt8, (u.lo >>> 40).toUInt8, (u.lo >>> 32).toUInt8,
     (u.lo >>> 24).toUInt8, (u.lo >>> 16).toUInt8, (u.lo >>> 8).toUInt8, u.lo.toUInt8]

/-- Build a UUID from 16 octets in network byte order. -/
def ofBytes (b : Vector UInt8 16) : UUID where
  hi := (b[0].toUInt64 <<< 56) ||| (b[1].toUInt64 <<< 48) ||| (b[2].toUInt64 <<< 40) |||
        (b[3].toUInt64 <<< 32) ||| (b[4].toUInt64 <<< 24) ||| (b[5].toUInt64 <<< 16) |||
        (b[6].toUInt64 <<< 8) ||| b[7].toUInt64
  lo := (b[8].toUInt64 <<< 56) ||| (b[9].toUInt64 <<< 48) ||| (b[10].toUInt64 <<< 40) |||
        (b[11].toUInt64 <<< 32) ||| (b[12].toUInt64 <<< 24) ||| (b[13].toUInt64 <<< 16) |||
        (b[14].toUInt64 <<< 8) ||| b[15].toUInt64

@[simp] theorem ofBytes_toBytes (u : UUID) : ofBytes (toBytes u) = u := by
  obtain ⟨hi, lo⟩ := u
  simp only [ofBytes, toBytes, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, mk.injEq]
  constructor <;> bv_decide

theorem toBytes_injective {u v : UUID} (h : u.toBytes = v.toBytes) : u = v := by
  rw [← ofBytes_toBytes u, ← ofBytes_toBytes v, h]

/-- The 16 octets of a UUID in network byte order, as a `ByteArray`. -/
def toByteArray (u : UUID) : ByteArray :=
  ⟨u.toBytes.toArray⟩

/-- Build a UUID from a `ByteArray` of exactly 16 octets in network byte order. -/
def ofByteArray? (b : ByteArray) : Option UUID :=
  if h : b.size = 16 then
    some (ofBytes ⟨b.data, h⟩)
  else
    none

@[simp] theorem size_toByteArray (u : UUID) : u.toByteArray.size = 16 :=
  u.toBytes.size_toArray

@[simp] theorem ofByteArray?_toByteArray (u : UUID) : ofByteArray? u.toByteArray = some u := by
  simp only [ofByteArray?, size_toByteArray, ↓reduceDIte]
  simp [toByteArray]

/-! ## 128-bit integers -/

/-- The UUID as a 128-bit vector (`hi` in the upper half). -/
def toBitVec (u : UUID) : BitVec 128 :=
  u.hi.toBitVec ++ u.lo.toBitVec

/-- Build a UUID from a 128-bit vector. -/
def ofBitVec (b : BitVec 128) : UUID where
  hi := ⟨b.extractLsb' 64 64⟩
  lo := ⟨b.extractLsb' 0 64⟩

@[simp] theorem ofBitVec_toBitVec (u : UUID) : ofBitVec u.toBitVec = u := by
  obtain ⟨hi, lo⟩ := u
  simp only [ofBitVec, toBitVec, mk.injEq]
  constructor <;> apply UInt64.eq_of_toBitVec_eq <;> bv_decide

@[simp] theorem toBitVec_ofBitVec (b : BitVec 128) : (ofBitVec b).toBitVec = b := by
  simp only [ofBitVec, toBitVec]
  bv_decide

/-- The UUID as an unsigned integer in `[0, 2^128)`. -/
def toNat (u : UUID) : Nat :=
  u.toBitVec.toNat

/-- Build a UUID from a natural number, keeping its lowest 128 bits. -/
def ofNat (n : Nat) : UUID :=
  ofBitVec (BitVec.ofNat 128 n)

@[simp] theorem ofNat_toNat (u : UUID) : ofNat u.toNat = u := by
  simp [ofNat, toNat]

theorem toNat_lt (u : UUID) : u.toNat < 2 ^ 128 :=
  u.toBitVec.isLt

end UUID

end
