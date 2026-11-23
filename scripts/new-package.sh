#!/usr/bin/env bash
# Scaffold a new library package under packages/.
#
#   scripts/new-package.sh <package-name> <ModuleName>
#   scripts/new-package.sh base64 Base64
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <package-name> <ModuleName>" >&2
  exit 2
fi
name="$1"
mod="$2"
if [[ ! "$name" =~ ^[a-z][a-z0-9-]*$ ]]; then
  echo "error: package name must be lowercase kebab-case: $name" >&2
  exit 2
fi
if [[ ! "$mod" =~ ^[A-Z][A-Za-z0-9]*$ ]]; then
  echo "error: module name must be UpperCamelCase: $mod" >&2
  exit 2
fi

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dir="$root/packages/$name"
if [[ -e "$dir" ]]; then
  echo "error: $dir already exists" >&2
  exit 1
fi

mkdir -p "$dir/$mod" "$dir/${mod}Test"
ln -s ../../lean-toolchain "$dir/lean-toolchain"

cat > "$dir/lakefile.toml" <<TOML
name = "$name"
version = "0.1.0"
description = "TODO"
defaultTargets = ["$mod"]
testDriver = "${mod}Test"

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

[[lean_lib]]
name = "$mod"
leanOptions = { linter.missingDocs = true }

# Tests: \`lake test\` builds and runs \`${mod}Test.lean\`, which imports the \`${mod}Test.*\` modules.
[[lean_lib]]
name = "tests"
globs = ["${mod}Test.+"]

[[lean_exe]]
name = "${mod}Test"
TOML

cat > "$dir/$mod.lean" <<LEAN
module

public import $mod.Basic
LEAN

cat > "$dir/$mod/Basic.lean" <<LEAN
module

/-!
# $mod
-/

@[expose] public section

namespace $mod

/-- A placeholder definition. -/
def hello : String := "Hello from $mod!"

end $mod

end
LEAN

cat > "$dir/${mod}Test/Basic.lean" <<LEAN
import $mod

#guard $mod.hello = "Hello from $mod!"
LEAN

cat > "$dir/${mod}Test.lean" <<LEAN
import ${mod}Test.Basic

def main : IO UInt32 := do
  IO.println "All $mod tests passed."
  return 0
LEAN

cat > "$dir/README.md" <<MD
# $name

TODO: describe the library.

\`\`\`toml
[[require]]
name = "$name"
git = "https://github.com/moshg/lean-playground"
rev = "main"
subDir = "packages/$name"
\`\`\`
MD

echo "Created packages/$name. Next:"
echo "  cd packages/$name && lake build && lake test"
echo "  and add it to the package table in README.md"
