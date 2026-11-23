#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lake_bin=${LAKE:-lake}
"$lake_bin" build WitnessExecutable >/dev/null
"$lake_bin" env lean --version
"$lake_bin" env lean -DwarningAsError=true examples/RestoreEvidence.lean
sh examples/range-ledger/check.sh
