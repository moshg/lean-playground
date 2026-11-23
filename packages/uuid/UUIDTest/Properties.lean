import UUID
import Std.Data.HashSet
import UUIDTest.Harness

/-!
# Runtime property tests

These exercise the compiled code paths (including `IO`-based generation) on many random inputs.
-/

namespace UUIDTest

open UUID

/-- Number of random samples per property. -/
def samples : Nat := 2000

/-- The ASCII uppercase form of a string. -/
def upper (s : String) : String := s.map Char.toUpper

def formatting : TestM Unit := do
  forAll "parse? ∘ toString = some" samples randomBits fun u => parse? u.toString == some u
  forAll "parse? ∘ toHexString = some" samples randomBits fun u => parse? u.toHexString == some u
  forAll "parse? ∘ toUrn = some" samples randomBits fun u => parse? u.toUrn == some u
  forAll "parse? ∘ toBraced = some" samples randomBits fun u => parse? u.toBraced == some u
  forAll "parse? accepts uppercase" samples randomBits fun u => parse? (upper u.toString) == some u
  forAll "toString is 36 lowercase chars" samples randomBits fun u =>
    let s := u.toString
    s.length == 36 && s == s.toLower
  forAll "string order = UUID order" samples
    (do return (← randomBits, ← randomBits))
    fun (a, b) => decide (a.toString < b.toString) == decide (a < b)

def conversions : TestM Unit := do
  forAll "ofByteArray? ∘ toByteArray = some" samples randomBits fun u =>
    ofByteArray? u.toByteArray == some u
  forAll "ofNat ∘ toNat = id" samples randomBits fun u => ofNat u.toNat == u
  forAll "compare agrees with toNat" samples (do return (← randomBits, ← randomBits))
    fun (a, b) => compare a b == compare a.toNat b.toNat

def v4 : TestM Unit := do
  forAll "v4 has version 4" samples UUID.v4 fun u =>
    u.version? == some .random && u.variant == .rfc9562
  let mut seen : Std.HashSet UUID := {}
  for _ in [0:samples] do
    seen := seen.insert (← UUID.v4)
  expectEq "v4 values are distinct" seen.size samples

def v7 : TestM Unit := do
  let before ← unixTimeMsNow
  let u ← UUID.v7
  let after ← unixTimeMsNow
  expectEq "v7 has version 7" u.version? (some .unixTime)
  expect "v7 timestamp is the current time"
    (match u.unixTimeMs? with
     | some t => before ≤ t && t ≤ after
     | none => false)
    fun _ => s!"{u.unixTimeMs?} not in [{before}, {after}]"
  let g ← V7Generator.new
  let mut prev ← g.next
  let mut increasing := true
  for _ in [0:samples * 5] do
    let next ← g.next
    unless prev < next do increasing := false
    prev := next
  expect "V7Generator output is strictly increasing" increasing
  expectEq "V7Generator output has version 7" prev.version? (some .unixTime)

def nameBased : TestM Unit := do
  forAll "v5 is deterministic and has version 5" 200 randomBits fun ns =>
    let a := UUID.v5 ns "name"
    a == UUID.v5 ns "name" && a.version? == some .sha1 && a != UUID.v5 ns "other"
  forAll "v3 is deterministic and has version 3" 200 randomBits fun ns =>
    let a := UUID.v3 ns "name"
    a == UUID.v3 ns "name" && a.version? == some .md5 && a != UUID.v3 ns "other"

/-- All runtime test suites. -/
def suites : List (String × TestM Unit) :=
  [("formatting", formatting), ("conversions", conversions), ("v4", v4), ("v7", v7),
   ("name-based", nameBased)]

end UUIDTest
