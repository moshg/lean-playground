module

public import UUID.Bytes

/-!
# Random UUIDs (version 4)

A version 4 UUID (RFC 9562 §5.4) consists of 122 random bits. `UUID.v4` draws them from
`IO.getRandomBytes`, which uses the operating system's cryptographically secure generator.
-/

@[expose] public section

namespace UUID

/-- 128 bits from the operating system's cryptographically secure random number generator. -/
def randomBits : IO UUID := do
  let bytes ← IO.getRandomBytes 16
  match ofByteArray? bytes with
  | some u => return u
  | none => throw <| IO.userError s!"IO.getRandomBytes returned {bytes.size} bytes, expected 16"

/-- The version 4 UUID built from the given bits (the version and variant bits are overwritten).
This is the pure core of `UUID.v4`. -/
def v4Of (bits : UUID) : UUID :=
  bits.withVersion .random

/-- Generate a fresh random (version 4) UUID. -/
def v4 : IO UUID :=
  v4Of <$> randomBits

@[simp] theorem version?_v4Of (bits : UUID) : (v4Of bits).version? = some .random := by
  simp [v4Of]

end UUID

end
