#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
LEAN_BIN="${LEAN_BIN:-lean}"
export LEAN_PATH=".:${LEAN_PATH:-}"
"$LEAN_BIN" --version
for source in Qualification Redundancy Tests; do
  "$LEAN_BIN" -DwarningAsError=true -o "$source.olean" "$source.lean"
done
controls=$(mktemp -d)
trap 'rm -rf "$controls"' EXIT
printf 'theorem rejected : True := by sorry\n' > "$controls/Admission.lean"
if "$LEAN_BIN" -DwarningAsError=true "$controls/Admission.lean" > "$controls/log" 2>&1; then
  echo 'FAIL: admission control passed'; exit 1
fi
grep -q 'sorry' "$controls/log"
printf 'theorem rejected : False := True.intro\n' > "$controls/Type.lean"
if "$LEAN_BIN" -DwarningAsError=true "$controls/Type.lean" > "$controls/log" 2>&1; then
  echo 'FAIL: type-error control passed'; exit 1
fi
grep -q 'error:' "$controls/log"
if grep -nE '\b(sorry|admit|axiom|native_decide)\b' Qualification.lean Redundancy.lean Tests.lean; then
  echo 'FAIL: forbidden proof token'; exit 1
fi
echo 'PASS: all three modules and both rejection controls'
