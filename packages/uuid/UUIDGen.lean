import UUID

/-!
# `uuidgen`: a small command-line front end

```
lake exe uuidgen                     # one random (v4) UUID
lake exe uuidgen v7 -n 3             # three strictly increasing v7 UUIDs
lake exe uuidgen v5 dns example.com  # name-based UUID
lake exe uuidgen inspect 017f22e2-79b0-7cc3-98c4-dc0c0c07398f
```
-/

open UUID

def usage : String := "\
Usage: uuidgen [COMMAND] [OPTIONS]

Commands:
  v4                    random UUID (default)
  v7                    time-ordered UUID
  v3 <namespace> <name> name-based UUID using MD5
  v5 <namespace> <name> name-based UUID using SHA-1
  nil | max             the Nil / Max UUID
  inspect <uuid>        show the version, variant and timestamp of a UUID

<namespace> is one of dns, url, oid, x500, or a UUID.

Options:
  -n, --count <N>       generate N UUIDs (v4 and v7 only)
  -u, --upper           print uppercase hexadecimal digits
  -h, --help            show this help"

structure Options where
  count : Nat := 1
  upper : Bool := false
  positional : Array String := #[]

def parseOptions : List String → Options → Except String Options
  | [], o => .ok o
  | arg :: rest, o =>
    if arg == "-n" || arg == "--count" then
      match rest with
      | n :: rest =>
        match n.toNat? with
        | some k => parseOptions rest { o with count := k }
        | none => .error s!"invalid count: {n}"
      | [] => .error s!"missing value for {arg}"
    else if arg == "-u" || arg == "--upper" then
      parseOptions rest { o with upper := true }
    else if arg.startsWith "-" then
      .error s!"unknown option: {arg}"
    else
      parseOptions rest { o with positional := o.positional.push arg }

def parseNamespace (s : String) : Except String UUID :=
  match s.toLower with
  | "dns" => .ok namespaceDNS
  | "url" => .ok namespaceURL
  | "oid" => .ok namespaceOID
  | "x500" => .ok namespaceX500
  | _ => (UUID.parse s).mapError fun e => s!"invalid namespace '{s}': {e}"

def variantName : Variant → String
  | .ncs => "NCS (reserved)"
  | .rfc9562 => "RFC 9562"
  | .microsoft => "Microsoft (reserved)"
  | .future => "future (reserved)"

def versionName : Version → String
  | .gregorian => "1 (Gregorian time)"
  | .dceSecurity => "2 (DCE Security)"
  | .md5 => "3 (name-based, MD5)"
  | .random => "4 (random)"
  | .sha1 => "5 (name-based, SHA-1)"
  | .reorderedGregorian => "6 (reordered Gregorian time)"
  | .unixTime => "7 (Unix time)"
  | .custom => "8 (custom)"

def inspect (u : UUID) : IO Unit := do
  IO.println s!"uuid:    {u}"
  IO.println s!"variant: {variantName u.variant}"
  match u.version? with
  | some v => IO.println s!"version: {versionName v}"
  | none =>
    let why :=
      if u.isNil then "Nil UUID"
      else if u.isMax then "Max UUID"
      else s!"raw value {u.versionNumber}"
    IO.println s!"version: none ({why})"
  if let some ms := u.unixTimeMs? then
    IO.println s!"unix_ts_ms: {ms}"

def run (o : Options) : IO UInt32 := do
  let fmt (u : UUID) : String := if o.upper then u.toString.toUpper else u.toString
  let emit (gen : IO UUID) : IO UInt32 := do
    for _ in [0:o.count] do
      IO.println (fmt (← gen))
    return 0
  match o.positional.toList with
  | [] | ["v4"] => emit UUID.v4
  | ["v7"] =>
    let g ← V7Generator.new
    emit g.next
  | ["nil"] => emit (pure UUID.nil)
  | ["max"] => emit (pure UUID.max)
  | ["v3", ns, name] | ["v5", ns, name] =>
    match parseNamespace ns with
    | .error e => IO.eprintln e; return 2
    | .ok ns =>
      let u := if o.positional[0]! == "v3" then UUID.v3 ns name else UUID.v5 ns name
      IO.println (fmt u)
      return 0
  | ["inspect", s] =>
    match UUID.parse s with
    | .error e => IO.eprintln e; return 1
    | .ok u => inspect u; return 0
  | _ =>
    IO.eprintln usage
    return 2

def main (args : List String) : IO UInt32 := do
  if args.contains "-h" || args.contains "--help" then
    IO.println usage
    return 0
  match parseOptions args {} with
  | .error e =>
    IO.eprintln s!"uuidgen: {e}\n\n{usage}"
    return 2
  | .ok o => run o
