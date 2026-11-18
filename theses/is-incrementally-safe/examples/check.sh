#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lean_bin=${LEAN:-lean}
"$lean_bin" --version
"$lean_bin" -DwarningAsError=true examples/PolicyMigration.lean
lake_bin=${LAKE:-lake}
"$lake_bin" env "$lean_bin" -DwarningAsError=true examples/NatReprInjective.lean
sh examples/range-ledger/check.sh
