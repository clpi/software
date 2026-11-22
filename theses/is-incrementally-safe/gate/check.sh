#!/bin/sh
# Check gate. Covers every tracked .lean file at HEAD:
#   1. toolchain matches lean-toolchain
#   2. lake build (lakefile sets -DwarningAsError=true for every library)
#   3. every tracked .lean file compiled on its own with -DwarningAsError=true;
#      files in gate/expected-red.txt must fail and keep their pinned sha256
#   4. gate/Axioms.lean: no declared axiom, no unsafe or opaque declaration, no axiom
#      beyond propext, Quot.sound, Classical.choice (sorry and native_decide fail here)
#   5. gate/escape_scan.py over every tracked .lean file
set -eu
cd "$(dirname "$0")/.."
LEAN=${LEAN:-lean}
LAKE=${LAKE:-lake}
fail=0

echo "== 1. toolchain"
want=$(sed 's/.*:v//' lean-toolchain)
have=$("$LEAN" --version)
echo "$have"
case "$have" in *"version $want,"*) ;; *) echo "FAIL toolchain: want $want"; exit 1;; esac
grep -q -- '-DwarningAsError=true' lakefile.lean || { echo "FAIL lakefile lost -DwarningAsError=true"; exit 1; }

echo "== 2. lake build"
"$LAKE" build 2>&1 | grep -E '^(error|warning)|Build completed|^✖' || true
"$LAKE" build >/dev/null 2>&1 || { echo "FAIL lake build"; exit 1; }
echo "lake build: ok"

echo "== 3. every tracked .lean file"
files=$( (git ls-files '*.lean'; git ls-files --others --exclude-standard '*.lean') | grep -v '^lakefile.lean$' | sort -u)
n=0; green=0; red=0
for f in $files; do
  n=$((n+1))
  entry=$(grep -v '^#' gate/expected-red.txt | grep "^$f |" || true)
  if [ -n "$entry" ]; then
    pin=$(echo "$entry" | cut -d'|' -f2 | tr -d ' ')
    got=$(sha256sum "$f" | cut -d' ' -f1)
    if [ "$pin" != "$got" ]; then echo "FAIL $f: expected-red record changed ($got)"; fail=1; continue; fi
    if "$LAKE" env "$LEAN" -DwarningAsError=true "$f" >/dev/null 2>&1; then
      echo "FAIL $f: expected red but it compiles; move it out of expected-red.txt"; fail=1
    else
      echo "red (expected, sha256 pinned)  $f"; red=$((red+1))
    fi
    continue
  fi
  if out=$("$LAKE" env "$LEAN" -DwarningAsError=true "$f" 2>&1); then
    green=$((green+1))
  else
    echo "FAIL $f"; echo "$out" | grep -E 'error' | head -5; fail=1
  fi
done
echo "files: $n, compiled clean: $green, expected red: $red"

echo "== 4. axiom walk"
if out=$("$LAKE" env "$LEAN" -DwarningAsError=true gate/Axioms.lean 2>&1); then
  echo "$out"
else
  echo "$out" | head -40; echo "FAIL axiom walk"; fail=1
fi

echo "== 5. escape scan"
python3 gate/escape_scan.py $(echo "$files"; echo lakefile.lean) || fail=1

if [ "$fail" -ne 0 ]; then echo "GATE: FAIL"; exit 1; fi
echo "GATE: PASS"
