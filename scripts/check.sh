#!/usr/bin/env bash
# Build (warnings are errors) and test every package, or only the ones named.
#
#   scripts/check.sh            # all packages
#   scripts/check.sh uuid       # just packages/uuid
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

if [[ $# -gt 0 ]]; then
  packages=("$@")
else
  packages=()
  for dir in packages/*/; do
    [[ -f "$dir/lakefile.toml" || -f "$dir/lakefile.lean" ]] && packages+=("$(basename "$dir")")
  done
fi

failed=()
for pkg in "${packages[@]}"; do
  dir="packages/$pkg"
  if [[ ! -d "$dir" ]]; then
    echo "error: no such package: $pkg" >&2
    exit 2
  fi
  echo "==> $pkg"
  if ! (cd "$dir" && lake build --wfail && { ! lake check-test || lake test; }); then
    failed+=("$pkg")
  fi
done

if [[ ${#failed[@]} -gt 0 ]]; then
  echo "FAILED: ${failed[*]}" >&2
  exit 1
fi
echo "All packages OK: ${packages[*]}"
