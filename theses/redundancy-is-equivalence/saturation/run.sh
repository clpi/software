#!/bin/sh
# Rebuild every measurement in results/. Needs cargo (std only, no
# crates) and python3. IDOL_LIB is a clpi/idol-lib checkout; the pin
# used for the committed results is recorded in results/pins.txt.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"
IDOL_LIB="${IDOL_LIB:?set IDOL_LIB to a clpi/idol-lib checkout}"
(cd wsat && cargo build --release -q)
W=wsat/target/release/wsat
mkdir -p results
git -C "$IDOL_LIB" rev-parse HEAD > results/pins.txt
python3 harvest.py "$IDOL_LIB" results/real.tsv
python3 suites.py results/suites.tsv
grep -P '\t(gen|cycle|valley)\t' results/suites.tsv > results/gen.tsv
grep -P '\trefuted\t' results/suites.tsv > results/unprovable.tsv
grep -P '\tac\t' results/suites.tsv > results/ac.tsv

ABL="w_nobeh=--no-beh w_noau=--no-au w_nobag=--no-bag w_nolin=--no-lin w_noent=--no-ent w_uni=--uni w_nobridge=--no-bridge w_nocredit=--no-credit w_nodiv=--no-dividend w_nodepth=--no-depth"

# real code, same contract: same rows, rules, witness points, fuel ceiling
python3 bench.py $W results/real.tsv results/real.json \
  "witness=" "greedy=--engine greedy" "saturate=--engine saturate" \
  "saturate_beh=--engine saturate --with-beh" \
  "sat_bound=--engine saturate --alloc 100000 --match 2000000 --rounds 60" \
  "eval=--engine eval" "decide=--engine decide" $ABL
# mechanism suites
python3 bench.py $W results/suites.tsv results/suites.json \
  "witness=" "greedy=--engine greedy" "saturate=--engine saturate" \
  "sat_bound=--engine saturate --alloc 100000 --match 2000000 --rounds 60" \
  "decide=--engine decide" $ABL
# generative rule on
python3 bench.py $W results/gen.tsv results/gen.json \
  "witness=--gen" "greedy=--engine greedy --gen" "saturate=--engine saturate --gen" \
  "w_naiveprov=--gen --prov-naive" "w_nodepth_nocredit=--gen --no-depth --no-credit" \
  "decide=--engine decide"
# divergence: unprovable rows, nobody gets the witness points, run to the bound
python3 bench.py $W results/unprovable.tsv results/divergence_gen.json \
  "sat_nogen=--engine saturate --alloc 20000 --match 400000 --rounds 200" \
  "sat_gen=--engine saturate --gen --alloc 20000 --match 400000 --rounds 200" \
  "witness_gen=--gen --no-beh"
# divergence: AC without the AC and linear macros
python3 bench.py $W results/ac.tsv results/divergence_ac.json \
  "sat_nomacro=--engine saturate --no-acrule --no-linrule --alloc 20000 --match 400000 --rounds 200" \
  "witness=" "witness_nomacro=--no-bag --no-lin" "decide=--engine decide"
# provenance overhead, same decisions (fixed rule order), 5 repeats
for i in 1 2 3 4 5; do
  python3 bench.py $W results/real.tsv results/overhead_$i.json \
    "prov=--record-only" "noprov=--record-only --no-prov"
done
gzip -f results/real.json results/overhead_*.json
python3 gate.py results
