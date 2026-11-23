module

public import UUID.Basic

/-!
# Formatting UUIDs as strings

The canonical textual form (RFC 9562 §4) is 32 lowercase hexadecimal digits split into five
hyphen-separated groups of 8-4-4-4-12 digits:

```
f81d4fae-7dec-11d0-a765-00a0c91e6bf6
```
-/

@[expose] public section

namespace UUID

/-- The hexadecimal digit for a nibble (`n < 16`), using lowercase letters. -/
def hexDigit (n : UInt64) : Char :=
  if n < 10 then Char.ofNat (n.toNat + '0'.toNat) else Char.ofNat (n.toNat - 10 + 'a'.toNat)

/-- The `i`-th nibble of the UUID (`i < 32`), counting from the most significant one. -/
def nibble (u : UUID) (i : Nat) : UInt64 :=
  let w := if i < 16 then u.hi else u.lo
  (w >>> ((15 - i % 16) * 4).toUInt64) &&& 0xF

/-- Append the hexadecimal digits of nibbles `[start, stop)` to `s`. -/
def pushNibbles (u : UUID) (s : String) (start stop : Nat) : String := Id.run do
  let mut s := s
  for i in [start:stop] do
    s := s.push (hexDigit (u.nibble i))
  return s

/-- The canonical hyphenated, lowercase form, e.g. `f81d4fae-7dec-11d0-a765-00a0c91e6bf6`. -/
protected def toString (u : UUID) : String :=
  let s := pushNibbles u "" 0 8
  let s := pushNibbles u (s.push '-') 8 12
  let s := pushNibbles u (s.push '-') 12 16
  let s := pushNibbles u (s.push '-') 16 20
  pushNibbles u (s.push '-') 20 32

/-- The 32 hexadecimal digits without hyphens, e.g. `f81d4fae7dec11d0a76500a0c91e6bf6`. -/
def toHexString (u : UUID) : String :=
  pushNibbles u "" 0 32

/-- The URN form (RFC 9562 §4), e.g. `urn:uuid:f81d4fae-7dec-11d0-a765-00a0c91e6bf6`. -/
def toUrn (u : UUID) : String :=
  "urn:uuid:" ++ u.toString

/-- The braced form used by Microsoft tooling, e.g. `{f81d4fae-7dec-11d0-a765-00a0c91e6bf6}`. -/
def toBraced (u : UUID) : String :=
  "{" ++ u.toString ++ "}"

instance : ToString UUID := ⟨UUID.toString⟩

/-- UUIDs are displayed as `uuid!"…"` literals (see `UUID.Literal`). -/
instance : Repr UUID where
  reprPrec u _ := "uuid!\"" ++ u.toString ++ "\""

end UUID

end
