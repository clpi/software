#!/usr/bin/env bash
# Run every gate of every old repo twice: in a fresh clone of the old repo, and at
# theses/<name>/ in a fresh clone of the consolidated repo. Compare exit codes and the
# tracked files each gate rewrites (receipts such as CHECK.log).
# Usage: compare-gates.sh SRC_DIR MONO_REPO GATES_TSV OUT_DIR [JOBS]
set -uo pipefail
SRC=$(cd "$1" && pwd); MONO=$(cd "$2" && pwd); GATES=$(cd "$(dirname "$3")" && pwd)/$(basename "$3"); OUT=$4; JOBS=${5:-4}
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
export SRC MONO OUT GATES
one_repo() {
  name=$1
  o="$OUT/runs/old/$name"; n="$OUT/runs/new/$name"
  rm -rf "$o" "$n"; mkdir -p "$(dirname "$o")" "$(dirname "$n")"
  git clone -q "$SRC/software-$name" "$o"
  git clone -q --no-checkout "$MONO" "$n" && git -C "$n" sparse-checkout set --no-cone "/theses/$name/" "/lean-toolchain" >/dev/null && git -C "$n" checkout -q main
  grep -P "^$name\t" "$GATES" | cut -f2 | while read g; do
    for side in old new; do
      if [ $side = old ]; then root=$o; else root=$n/theses/$name; fi
      repo=$([ $side = old ] && echo $o || echo $n)
      start=$(date +%s)
      case "$g" in
        lake:*) d=${g#lake:}; (cd "$root/$d" && timeout 1800 lake build) ;;
        *.py)   (cd "$root/$(dirname $g)" && timeout 1800 python3 "$(basename $g)") ;;
        *)      (cd "$root/$(dirname $g)" && timeout 1800 bash "$(basename $g)") ;;
      esac > "$OUT/log.$side.$name.$(echo $g | tr '/:' '__')" 2>&1
      rc=$?
      dur=$(( $(date +%s) - start ))
      # tracked files changed by the gate, relative to the thesis root
      if [ $side = old ]; then changed=$(git -C "$repo" status --porcelain -uno | awk '{print $2}' | sort | tr '\n' ' ');
      else changed=$(git -C "$repo" status --porcelain -uno | awk '{print $2}' | sed "s#^theses/$name/##" | sort | tr '\n' ' '); fi
      diffh=$( (cd "$repo" && git diff -- . | sed -e "s#^\(diff --git\|---\|+++\|index\) .*##" | sha256sum | cut -c1-12) )
      printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$name" "$g" "$side" "$rc" "$dur" "$diffh" "${changed:--}"
      (cd "$repo" && git checkout -q -- . 2>/dev/null)
    done
  done
}
export -f one_repo
cut -f1 "$GATES" | sort -u | xargs -P "$JOBS" -I{} bash -c 'one_repo {}' > "$OUT/results.tsv"
echo "done: $(wc -l < "$OUT/results.tsv") runs"
