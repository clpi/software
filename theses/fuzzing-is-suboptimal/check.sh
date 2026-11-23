#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
LEAN="${LEAN:-lean}"
"$LEAN" --version | grep -F 'version 4.19.0'
export LEAN_PATH=.
sources=(Fuzzing.lean Certificate.lean Tests.lean)
forbidden='\b(sorry|admit|axiom|native_decide)\b'
if grep -nE "$forbidden" "${sources[@]}"; then
  echo 'FAIL: forbidden proof token'; exit 1
fi
logs=$(mktemp -d)
trap 'rm -rf "$logs"' EXIT
for module in Fuzzing Certificate Tests; do
  "$LEAN" -DwarningAsError=true -o "$module.olean" "$module.lean" | tee "$logs/$module.log"
  if grep -q 'sorryAx' "$logs/$module.log"; then
    echo 'FAIL: admitted theorem in axiom report'; exit 1
  fi
done
