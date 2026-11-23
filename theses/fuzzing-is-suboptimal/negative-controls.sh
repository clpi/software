#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
LEAN="${LEAN:-lean}"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
printf 'theorem bad : False := by sorry\n' > "$tmp/Hole.lean"
if "$LEAN" -DwarningAsError=true "$tmp/Hole.lean" > "$tmp/hole.log" 2>&1; then
  echo 'ERROR: admitted proof hole'; exit 1
fi
printf 'theorem bad : False := by exact True.intro\n' > "$tmp/False.lean"
if "$LEAN" -DwarningAsError=true "$tmp/False.lean" > "$tmp/false.log" 2>&1; then
  echo 'ERROR: accepted false derivation'; exit 1
fi
# Exercise the actual release gate, including tokens Lean does not warn about.
cp check.sh Fuzzing.lean Certificate.lean "$tmp/"
for token in sorry admit axiom native_decide; do
  printf '%s\n' "$token" > "$tmp/Tests.lean"
  if LEAN="$LEAN" bash "$tmp/check.sh" > "$tmp/scan.log" 2>&1; then
    echo "ERROR: gate accepted $token"; exit 1
  fi
  grep -q 'FAIL: forbidden proof token' "$tmp/scan.log"
done
echo 'PASS: proof hole, false derivation, and four actual-gate forbidden-token controls rejected' 
