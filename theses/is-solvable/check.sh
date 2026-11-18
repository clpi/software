#!/bin/sh
set -eu
cd "$(dirname "$0")"
LEAN="${LEAN:-lean}"
export LEAN_PATH=".:${LEAN_PATH:-}"
if grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' ./*.lean; then
  echo 'Rejected proof escape hatch' >&2; exit 1
fi
TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT HUP INT TERM
"$LEAN" --version
for f in Qualification ExecutableClosure Hyperlattice WitnessExecutable WitnessTests; do
  if "$LEAN" -DwarningAsError=true -o "$f.olean" "$f.lean" > "$TMP" 2>&1; then
    cat "$TMP"
  else
    cat "$TMP"; exit 1
  fi
  if grep -Eq 'sorryAx|error:|warning:' "$TMP"; then exit 1; fi
done
printf 'PASS: five Lean modules, all kernel checks and executable guards.\n'
