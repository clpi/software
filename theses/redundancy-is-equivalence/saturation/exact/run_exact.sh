#!/bin/sh
# Finest-grain comparison: every 64-bit input, every callee. Needs the
# results of ../run.sh, python3 with z3-solver, and cargo (egg 0.9.5).
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE/.."
IDOL_LIB="${IDOL_LIB:?set IDOL_LIB to a clpi/idol-lib checkout}"
W=wsat/target/release/wsat
(cd egg-floor && cargo build --release -q)
E=egg-floor/target/release/egg-floor
mkdir -p results/exact
python3 harvest.py "$IDOL_LIB" results/cross.tsv --cross
python3 bench.py $W results/cross.tsv results/cross.json \
  "decide=--engine decide" "witness=" "greedy=--engine greedy" "saturate=--engine saturate" \
  "saturate_beh=--engine saturate --with-beh" \
  "sat_bound=--engine saturate --alloc 100000 --match 2000000 --rounds 60"
gzip -f results/cross.json
for c in real suites cross; do
  python3 exact/xdecide.py $W results/$c.tsv > results/exact/${c}_xdecide.jsonl
  python3 exact/z3only.py results/$c.tsv > results/exact/${c}_z3.jsonl
  t0=$(python3 -c 'import time;print(time.perf_counter())')
  $E 10000 2 < results/$c.tsv > results/exact/${c}_egg.jsonl
  python3 -c "import time,json;print(json.dumps({'wall_s':round(time.perf_counter()-$t0,4)}))" > results/exact/${c}_egg.wall
done
python3 exact/gate_exact.py results
