module

public import UUID.Basic

/-!
# Parsing UUIDs from strings

`UUID.parse` accepts the following forms. Hexadecimal digits may be upper- or lowercase.

| Form        | Example                                         |
|-------------|-------------------------------------------------|
| hyphenated  | `f81d4fae-7dec-11d0-a765-00a0c91e6bf6`          |
| simple      | `f81d4fae7dec11d0a76500a0c91e6bf6`              |
| braced      | `{f81d4fae-7dec-11d0-a765-00a0c91e6bf6}`        |
| URN         | `urn:uuid:f81d4fae-7dec-11d0-a765-00a0c91e6bf6` |

The braced and URN forms may wrap either the hyphenated or the simple form.
-/

@[expose] public section

namespace UUID

/-- The reason a string could not be parsed as a UUID. -/
inductive ParseError where
  /-- After removing braces or a `urn:uuid:` prefix, the input was neither 32 nor 36
  characters long. `length` is the length of what remained. -/
  | invalidLength (length : Nat)
  /-- The character `char` at (zero-based) index `index` of the input is not allowed there. -/
  | invalidChar (char : Char) (index : Nat)
deriving Repr, DecidableEq, Inhabited

instance : ToString ParseError where
  toString
    | .invalidLength n =>
      s!"invalid UUID length: expected 32 or 36 characters (excluding braces or a \
        `urn:uuid:` prefix), found {n}"
    | .invalidChar c i => s!"invalid character {repr c} at index {i} of UUID"

/-- The value of a hexadecimal digit (either case). -/
def hexValue? (c : Char) : Option UInt64 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt64
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt64
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt64
  else none

/-- Does the hyphenated form have a `-` at this position? -/
def isHyphenPos (i : Nat) : Bool :=
  i == 8 || i == 13 || i == 18 || i == 23

/--
Parse the 32 hex digits of a UUID, accumulating the first 16 nibbles into `hi` and the rest into
`lo`. `i` is the index within the body, `offset` the index of the body within the input (for
error messages) and `k` the number of nibbles read so far.
-/
def parseDigits (hyphenated : Bool) (offset : Nat) :
    List Char → (i k : Nat) → (hi lo : UInt64) → Except ParseError UUID
  | [], _, _, hi, lo => .ok ⟨hi, lo⟩
  | c :: cs, i, k, hi, lo =>
    if hyphenated && isHyphenPos i then
      if c = '-' then parseDigits hyphenated offset cs (i + 1) k hi lo
      else .error (.invalidChar c (offset + i))
    else
      match hexValue? c with
      | none => .error (.invalidChar c (offset + i))
      | some d =>
        if k < 16 then parseDigits hyphenated offset cs (i + 1) (k + 1) ((hi <<< 4) ||| d) lo
        else parseDigits hyphenated offset cs (i + 1) (k + 1) hi ((lo <<< 4) ||| d)

/-- Remove an optional `urn:uuid:` prefix (case-insensitive) or surrounding braces.
Returns the remaining characters and their offset within the input. -/
def stripWrapper (cs : List Char) : List Char × Nat :=
  if (cs.take 9).map Char.toLower = "urn:uuid:".toList then
    (cs.drop 9, 9)
  else if cs.head? = some '{' && cs.getLast? = some '}' then
    ((cs.drop 1).dropLast, 1)
  else
    (cs, 0)

/-- Parse a UUID in any of the supported forms, reporting why parsing failed. -/
def parse (s : String) : Except ParseError UUID :=
  let (body, offset) := stripWrapper s.toList
  match body.length with
  | 32 => parseDigits false offset body 0 0 0 0
  | 36 => parseDigits true offset body 0 0 0 0
  | n => .error (.invalidLength n)

/-- Parse a UUID in any of the supported forms. -/
def parse? (s : String) : Option UUID :=
  (parse s).toOption

/-- Parse a UUID in any of the supported forms, panicking on failure. -/
def parse! (s : String) : UUID :=
  match parse s with
  | .ok u => u
  | .error e => panic! toString e

end UUID

end
