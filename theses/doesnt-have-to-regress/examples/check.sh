#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lean_bin=${LEAN:-lean}
"$lean_bin" --version
"$lean_bin" -DwarningAsError=true examples/LogBatching.lean
python3 examples/replay.py
