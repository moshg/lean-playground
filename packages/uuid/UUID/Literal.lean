module

public import UUID.Parse
public meta import UUID.Parse

/-!
# `uuid!` literals

`uuid!"f81d4fae-7dec-11d0-a765-00a0c91e6bf6"` is a term of type `UUID` that is parsed at
*macro-expansion time*: a malformed literal is a compile error rather than a runtime panic, and
the literal expands to the constant `UUID.mk 0xf81d4fae7dec11d0 0xa76500a0c91e6bf6`.

Any form accepted by `UUID.parse` may be used.

This is implemented as a `macro` rather than a term elaborator on purpose: macros only need
`Init`, so using `uuid!` does not link the whole `Lean` package into executables.
-/

public section

namespace UUID

/-- A UUID literal, checked at compile time: `uuid!"f81d4fae-7dec-11d0-a765-00a0c91e6bf6"`. -/
macro "uuid!" s:str : term => do
  match UUID.parse s.getString with
  | .ok u =>
    let hi := Lean.Syntax.mkNumLit (toString u.hi.toNat)
    let lo := Lean.Syntax.mkNumLit (toString u.lo.toNat)
    `(UUID.mk $hi $lo)
  | .error e => Lean.Macro.throwErrorAt s (toString e)

end UUID

end
