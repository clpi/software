#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lean_bin=${LEAN:-lean}
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build"
mkdir -p "$build/SoftwareIsComposable"
"$lean_bin" -DwarningAsError=true -o "$build/SoftwareIsComposable/Profile.olean" "SoftwareIsComposable/Profile.lean" >/dev/null
"$lean_bin" -DwarningAsError=true -o "$build/SoftwareIsComposable/Admission.olean" "SoftwareIsComposable/Admission.lean" >/dev/null
"$lean_bin" -DwarningAsError=true -o "$build/SoftwareIsComposable/Composition.olean" "SoftwareIsComposable/Composition.lean" >/dev/null
"$lean_bin" --version
"$lean_bin" -DwarningAsError=true examples/ReleasePartition.lean
