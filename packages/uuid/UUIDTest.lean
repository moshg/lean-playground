import UUIDTest.Static
import UUIDTest.Properties

/-!
# UUID test driver

Run with `lake test`. Building this executable checks the compile-time tests in
`UUIDTest.Static`; running it executes the property tests in `UUIDTest.Properties`.
-/

def main : IO UInt32 :=
  UUIDTest.runTests UUIDTest.suites
