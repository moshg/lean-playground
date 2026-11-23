module

public import UUID.Hash.Common

/-!
# SHA-1 (RFC 3174 / FIPS 180-4)

Used for version 5 (name-based) UUIDs. SHA-1 is cryptographically broken; RFC 9562 keeps it only
for backward compatibility of UUIDv5.
-/

@[expose] public section

namespace UUID.Hash

/-- The SHA-1 digest (20 bytes) of `msg`. -/
def sha1 (msg : ByteArray) : ByteArray := Id.run do
  let m := pad msg (bigEndian := true)
  let mut h0 : UInt32 := 0x67452301
  let mut h1 : UInt32 := 0xEFCDAB89
  let mut h2 : UInt32 := 0x98BADCFE
  let mut h3 : UInt32 := 0x10325476
  let mut h4 : UInt32 := 0xC3D2E1F0
  for chunk in [0:m.size / 64] do
    let base := chunk * 64
    let mut w : Array UInt32 := Array.emptyWithCapacity 80
    for t in [0:16] do
      w := w.push (readBE m (base + 4 * t))
    for t in [16:80] do
      w := w.push (rotl (w[t - 3]! ^^^ w[t - 8]! ^^^ w[t - 14]! ^^^ w[t - 16]!) 1)
    let mut a := h0
    let mut b := h1
    let mut c := h2
    let mut d := h3
    let mut e := h4
    for t in [0:80] do
      let (f, k) :=
        if t < 20 then ((b &&& c) ||| (~~~b &&& d), (0x5A827999 : UInt32))
        else if t < 40 then (b ^^^ c ^^^ d, 0x6ED9EBA1)
        else if t < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8F1BBCDC)
        else (b ^^^ c ^^^ d, 0xCA62C1D6)
      let temp := rotl a 5 + f + e + k + w[t]!
      e := d
      d := c
      c := rotl b 30
      b := a
      a := temp
    h0 := h0 + a
    h1 := h1 + b
    h2 := h2 + c
    h3 := h3 + d
    h4 := h4 + e
  return ByteArray.emptyWithCapacity 20
    |> (pushBE · h0) |> (pushBE · h1) |> (pushBE · h2) |> (pushBE · h3) |> (pushBE · h4)

end UUID.Hash

end
