#!/bin/sh
set -eu
cd "$(dirname "$0")"
LAKE="${LAKE:-lake}"
# The closure core is imported from software-optimality at the pin in
# lakefile.lean (resolved in lake-manifest.json), not copied into this tree.
if grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' ./*.lean examples/*.lean examples/*/*.lean; then
  echo 'Rejected proof escape hatch' >&2; exit 1
fi
TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT HUP INT TERM
"$LAKE" env lean --version
if ! "$LAKE" build > "$TMP" 2>&1; then cat "$TMP"; exit 1; fi
cat "$TMP"
if grep -Eq 'sorryAx|error:|warning:' "$TMP"; then exit 1; fi
STD='(propext|Classical\.choice|Quot\.sound)'
if grep -E 'depends on axioms' "$TMP" | grep -vE "axioms: \[$STD(, $STD)*\]"; then
  echo 'Rejected nonstandard axiom' >&2; exit 1
fi
printf 'PASS: four Lean modules on the imported optimality core; kernel checks, executable guards and Pareto controls.\n'
