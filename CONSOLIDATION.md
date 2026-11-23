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
run-gates.sh          runs every gate: copies check, shared core and bridges, every thesis
shared/               one copy of each reconciled file; shared/core is the canonical Lean library
CONCEPTS.md           concept index: canonical definition, every variant, its bridge or why it differs
lean-toolchain        v4.19.0, same as every thesis
```

Stage 1 (the commit tagged `import`) moves nothing between theses and edits no file under `theses/`.
Each old repo maps to exactly one directory, so every old path `repo:path` is
`theses/<name>/path`.

Stage 2, reconciliation (done on this branch, after the import commit tagged `import`):

1. Identical copies: 12 files stored once under `shared/` (plus the root `lean-toolchain`);
   107 old paths are symlinks to them and still read the same bytes. Three Lean copy groups
   (`Qualification.lean` x3, `Redundancy.lean` x2, `Canon.lean` x2) stay as files because Lake
   refuses a module whose real path is outside its package; `consolidation/check-copies.py`
   fails if any copy drifts. `consolidation/reconcile-audit.py REPO import HEAD` proves every
   imported file is unchanged or reads identical bytes through its link: 1,476 unchanged,
   107 linked, 0 problems.
2. One canonical concept each: `shared/core` (Lake package `software-core`) defines
   `Derives`, `Closed`, `NoWorse`, `Dominates` once. 11 bridges, 16 theorems, prove each
   thesis's own definition equivalent, compiled from the thesis's own source
   (see `CONCEPTS.md`). Variants that are a different concept are listed with the reason.
   Controls: a false bridge (Dominates iff NoWorse) and a mutated thesis definition both make
   `shared/core/check.sh` exit 1.
3. One version per Lean dependency: tried and reverted. Path requires made 8 of 9 dependents
   build at current heads, but the theses' own gates require immutable Git pins
   (is-composable, is-incrementally-certifiable), audited pins (doesnt-have-to-regress, whose
   Readings audit proves a flaw the current is-quantifiable fixes) and `--wfail` (optimality,
   which rejects warnings in the current is-quantifiable head). It needs a hosted immutable home
   for the pins; `consolidation/repin.py` then keeps every pin exact (tested on all 9).

Not done: repointing theses at `SoftwareCore` and deleting their own definitions. The bridges
make that safe, but each repoint rewrites that thesis's proofs and gate, so it is per-thesis work.

Reduction (import commit vs this branch, theses/ + shared/): stored files 1,583 to 1,505;
duplicate stored copies 140 to 45 (the rest are .gitignore, empty files, the 3 guarded Lean
groups and duplicates inside one thesis); 13 distinct definitions of 4 concepts now proven equal
to 4 canonical ones. Bytes fall only 0.3% (41.26 MB to 41.12 MB): the theses were mostly
distinct work, not copies.

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
