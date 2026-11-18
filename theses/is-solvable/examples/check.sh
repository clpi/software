#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lean_bin=${LEAN:-lean}
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build"
"$lean_bin" -DwarningAsError=true -o "$build/Qualification.olean" "Qualification.lean" >/dev/null
"$lean_bin" -DwarningAsError=true -o "$build/ExecutableClosure.olean" "ExecutableClosure.lean" >/dev/null
"$lean_bin" -DwarningAsError=true -o "$build/Hyperlattice.olean" "Hyperlattice.lean" >/dev/null
"$lean_bin" -DwarningAsError=true -o "$build/WitnessExecutable.olean" "WitnessExecutable.lean" >/dev/null
"$lean_bin" --version
"$lean_bin" -DwarningAsError=true examples/RestoreEvidence.lean
