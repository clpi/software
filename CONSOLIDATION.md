# Consolidation of the clpi/software-* repos

Prepared 2026-11-23. Nothing was created, pushed, archived, renamed or deleted on GitHub.
This repo exists only locally until Chris says yes.

## What overlaps (measured at the default-branch heads listed in `consolidation/imports.txt`)

32 repos, 1,583 tracked files, 4,406 theorem/lemma declarations, 240 Lean files, one toolchain
(every one of the 33 Lean projects pins `leanprover/lean4:v4.19.0`).

Byte-level duplication is small. Structural duplication is large.

- Exact duplicate files: 128 of 1,583 (8%) also exist byte-for-byte in another repo. 30 more are
  60%+ line-identical to a file in another repo. Tables: `consolidation/overlap-by-repo.tsv`,
  `consolidation/dup-blobs.tsv`, `consolidation/neardup.tsv`.
- Duplicate theorems: 167 of 4,406 (3.8%) have a whitespace-normalized body identical to one in
  another repo. Biggest pairs: frontier-is-solvable / redundant-compute-expands (24, `Canon.lean`),
  benchmarking / testing-is-redundant (20, `Qualification.lean` + `Redundancy.lean`),
  is-composable / is-incrementally-certifiable (18, `Legacy` copy), is-bidirectional /
  losses-are-compositional (13), optimality / benchmarking / testing (10 each).
- The shared incremental gate: `gate.py` (and `.gitignore`) is byte-identical in
  redundant-compute-expands, is-reversible, is-a-parametric-language-model and
  has-a-highest-minimal-axis. `frontier.py` and `fuzz/fuzz_s1.py` are shared by two of them.
  The other 17 files in those four directories are per-system (s1, s2, s3, axis) and differ.
- Scaffolding copied everywhere: `proof/check.sh` in 12 repos (8 byte-identical, 4 variants at
  84-96%); `lean-toolchain` in 30.
- Re-implemented concepts (same name, different body): `Derives` in 7 repos (5 variants),
  `Contract` 7 (10), `Closed` 6 (4), `Dominates` 5 (5), `noWorse` 5 (5), `Receipt` 5 (7).
  This is the real overlap, and merging it is proof work, not file moves.
- Version drift by construction: 19 Lake git pins across 8 repos point at 7 different commits of
  is-quantifiable and 5 of optimality, none at a current head.

## Layout

```
theses/<name>/        each old repo, verbatim, full history (name = repo minus "software-")
consolidation/        build.sh, verify.py, compare-gates.sh, repin.py, manifest, maps, overlap tables
run-gates.sh          runs every gate of every thesis
lean-toolchain        v4.19.0, same as every thesis
```

Stage 1 (this repo) moves nothing between theses and edits no file under `theses/`.
Each old repo maps to exactly one directory, so every old path `repo:path` is
`theses/<name>/path`.

Stage 2, each its own reviewed change, each with old-vs-new gate receipts:
1. Repin Lake requires to this repo with `repin.py` (same pinned trees, new URL plus `subDir`).
   Tested locally on all 9 Lake projects that require a sibling (8 theses plus
   doesnt-need-review/statement): all build, every dependency resolved from this repo at the
   rewritten pin, zero clones from GitHub.
2. `shared/incremental/` holds the one `gate.py`, `frontier.py`, `fuzz_s1.py`; the four theses
   keep their adapters and call the shared gate.
3. `shared/lean/check.sh` replaces the 8 identical `proof/check.sh`; the 4 variants stay until
   their differences are folded in as options.
4. `Qualification.lean`, `Redundancy.lean`, `Canon.lean`, the composable `Legacy` copy and the
   certificate checker each kept once, imported where copied.
5. Concept unification (`Derives`, `Dominates`, `Closed`, ...) only with an equivalence theorem
   per variant; a variant that is not equivalent stays and is named for what it is.

## History

`build.sh` runs `git filter-repo --to-subdirectory-filter theses/<name> --preserve-commit-hashes`
on every repo and merges the default branch with `--allow-unrelated-histories`. Commit messages
keep their original SHA references. Every other branch and every PR head is kept as
`archive/<name>/<branch>` and `archive/<name>/pr/<n>`; tags as `<name>/<tag>`. Old-to-new commit
maps are in `consolidation/maps/`.

## Proof that nothing is lost

`consolidation/verify.py SRC MONO MAPS` checks by git object hash:
every commit reachable from any old ref is mapped, with `theses/<name>` tree equal to the old
root tree and identical author, date and message; every branch, PR head and tag has its mapped
ref; `main:theses/<name>` equals each old default tree; nothing else sits at top level; and an
inventory of every file, theorem, gate and receipt is re-derived from this repo's bytes
(`consolidation/manifest.tsv`). Three negative controls (one byte appended, one PR ref deleted,
one Lean file removed) each make it exit 1.

## Gates

`consolidation/compare-gates.sh` runs every gate (90: each `check.sh`/`run.sh` up to depth 3,
emergence rung checkers, `lake build` at every lakefile) in a fresh clone of the old repo and at
`theses/<name>` in a fresh clone of this repo, then compares exit codes and the tracked files each
gate rewrites. Results (`consolidation/gates-results.tsv`, columns thesis, gate, side, exit,
seconds, diff hash, files rewritten):

- 90 gates, exit code identical old vs new in all 90. 81 pass on both sides.
- 9 fail on both sides for reasons that predate this repo: the four emergence rung checkers need a
  battery argument and run logs that are not committed; doesnt-need-review `check.sh` refuses its
  own toolchain line when Lake prints clone messages into it; has-a-highest-minimal-axis
  `proof/check.sh` needs `solver/fixtures/arena.json`, which is not committed; two
  redundant-compute-expands examples need `OPT`/`IL`/`IQ` checkouts passed in; is-incrementally-safe
  `examples/check.sh` needs `lake build` first (rerun after the build: exit 0 on both sides).
- Receipts rewritten by gates are byte-identical old vs new except 3 gates whose receipts embed
  absolute paths and wall-clock seconds; after normalizing those two things they are identical.

## Cutover (needs Chris's yes)

1. Create the repo, push `main`, push `archive/*` and tags.
2. Open PRs: merge or close in the old repo first; otherwise re-open from `archive/<name>/pr/<n>`
   (paths are only prefixed, so they apply cleanly).
3. Repoint the daily monotone ingest routine from software-redundant-compute-expands to this repo
   at `theses/redundant-compute-expands`, and swap that repo in this project's repository list.
4. Archive (never delete) the old repos with a README pointer. Old Lake pins inside history still
   name the old URLs, so they must stay readable.
