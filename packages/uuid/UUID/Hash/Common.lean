module

/-!
# Shared helpers for the Merkle–Damgård hash functions (MD5, SHA-1)

These are deliberately simple, allocation-light implementations intended for name-based UUIDs.
They are **not** constant-time and must not be used for anything security-sensitive.
-/

@[expose] public section

namespace UUID.Hash

/-- Rotate a 32-bit word left by `n` bits (`0 < n < 32`). -/
@[inline] def rotl (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/--
Merkle–Damgård padding shared by MD5 and SHA-1: append `0x80`, then zeros until the length is
`56 mod 64`, then the message length in bits as a 64-bit integer (big- or little-endian).
-/
def pad (msg : ByteArray) (bigEndian : Bool) : ByteArray := Id.run do
  let bitLen : UInt64 := (msg.size * 8).toUInt64
  let zeros := (64 + 56 - (msg.size + 1) % 64) % 64
  let mut b := msg.push 0x80
  for _ in [0:zeros] do
    b := b.push 0
  for i in [0:8] do
    let shift := if bigEndian then 56 - 8 * i else 8 * i
    b := b.push (bitLen >>> shift.toUInt64).toUInt8
  return b

/-- Read a big-endian 32-bit word at byte offset `i`. -/
@[inline] def readBE (b : ByteArray) (i : Nat) : UInt32 :=
  (b[i]!.toUInt32 <<< 24) ||| (b[i + 1]!.toUInt32 <<< 16) |||
  (b[i + 2]!.toUInt32 <<< 8) ||| b[i + 3]!.toUInt32

/-- Read a little-endian 32-bit word at byte offset `i`. -/
@[inline] def readLE (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 ||| (b[i + 1]!.toUInt32 <<< 8) |||
  (b[i + 2]!.toUInt32 <<< 16) ||| (b[i + 3]!.toUInt32 <<< 24)

/-- Append a 32-bit word in big-endian order. -/
@[inline] def pushBE (b : ByteArray) (x : UInt32) : ByteArray :=
  b |>.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8
    |>.push x.toUInt8

/-- Append a 32-bit word in little-endian order. -/
@[inline] def pushLE (b : ByteArray) (x : UInt32) : ByteArray :=
  b |>.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8
    |>.push (x >>> 24).toUInt8

/-- Lowercase hexadecimal encoding of a byte string (handy for testing digests). -/
def toHex (b : ByteArray) : String :=
  b.foldl (init := "") fun s x =>
    let d (n : UInt8) : Char :=
      if n < 10 then Char.ofNat (n.toNat + 48) else Char.ofNat (n.toNat + 87)
    (s.push (d (x >>> 4))).push (d (x &&& 0xF))

end UUID.Hash

end
