#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lean_bin=${LEAN:-lean}
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build"
"$lean_bin" -DwarningAsError=true -o "$build/Frontier.olean" "Frontier.lean" >/dev/null
"$lean_bin" --version
"$lean_bin" -DwarningAsError=true examples/ReplicaPlacement.lean
