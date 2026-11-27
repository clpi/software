# grh-compact: measured cuts to the Lean proof of GRH

Upstream: [lsernau/grh-lean](https://github.com/lsernau/grh-lean) at commit `72fead102f663d5c`, directory `grh/` (readable edition, Apache-2.0, see `LICENSE` and `NOTICE.upstream`). Nothing here is pushed upstream. Every cut is a patch against that commit, kept append only: a later cut never edits an earlier one.

## What a cut must satisfy

1. The five theorem statements in `Main.lean` and `Statements.lean` are untouched.
2. `#print axioms` for all five stays `[propext, Classical.choice, Quot.sound]`.
3. `lake build Main` succeeds on the patched tree (all 9,850 jobs).
4. The transitive constant closure of `riemannHypothesis` (types and values, Mathlib included) strictly shrinks.

## Results

| Cut | What changed | Closure of `riemannHypothesis` | Removed / added |
|---|---|---|---|
| baseline | upstream `72fead10` | 219,974 | |
| 1 | `New.exists_eigenvector_of_commute` proved without Lie algebras (least-dimensional invariant subspace, plus Mathlib `Eigenspace.Pi`) | | |
| 2 | Cyclic Hilbert 90 at `TateIndexFormula.lean:443` proved from Dedekind's independence of characters, no group cohomology | | |
| 1+2 | both, built together | 217,911 | 2,070 removed (528 `Lie*`, 375 `groupCohomology`/`Rep`), 7 added |
| 3 | pairs `a < b` in `Fin r` counted row by row, not with `Fintype.card_product_filter_lt` | | |
| 4 | p-adic limit `u^(q^n) → 1` from an ultrametric estimate, not Mahler series | | |
| 1-4 | all four, built together | 217,742 | 175 more removed (as predicted), 6 added |
| 5 | `GL n F` transitive on projective space by extending a linear map, not via `SL` primitivity | 217,511 | 232 removed, 1 added |
| 6 | oscillatory Fourier bound by `Real.fourier_fderiv` on a compactly supported function, not Schwartz maps | | |
| 7 | `Subsingleton (Unit ⧸ ⊤)` given directly, not found through Z-groups | | |
| 1-7 | all seven, built together | 216,834 | 682 more removed, 5 added |

Build: `lake build Main` 9,850 jobs, exit 0, 3,630 s. Axioms: `receipts/axioms_compact.out`. Exact constant lists: `receipts/removed_constants.txt`, `receipts/added_constants.txt`.

## Where the proof's weight is

- Declaration-level usage: `riemannHypothesis` uses 98.6% of the project's declaration lines; the five theorems together add 37 lines. There is no dead code to delete.
- Dominator tree of the closure (`tools/domfull.py`, `receipts/dominators_*.tsv`): for every constant, what leaves the closure if only that constant's proof changes. `New.exists_isRegularFamily` (the Selmer and Galois-representation family) alone carries 34.7% of the project's lines. Of the 170,159 Mathlib and core constants, 41,219 are reached through exactly one local lemma; those are the cuts this method can reach. `receipts/FRONTIER.md` ranks them.
- The regular family is used as a per-prime congruence bound on the space of lifts, per dimension and independent of the ambient dimension. Both Galois-free bounds tried (Hecke resultant, Gram determinant) lose a factor of the ambient dimension. No compact replacement found.

## Reproduce

```
git clone https://github.com/lsernau/grh-lean && cd grh-lean && git checkout 72fead102f663d5c
git apply ../software/grh-compact/cuts-1-2.patch ../software/grh-compact/cut-3.patch ../software/grh-compact/cut-4.patch ../software/grh-compact/cut-5.patch ../software/grh-compact/cut-6.patch ../software/grh-compact/cut-7.patch
cd grh && lake build Main
lake env lean ../../software/grh-compact/tools/Axioms.lean
lake env lean ../../software/grh-compact/tools/MainEdgesFull.lean   # writes edges_full.tsv, prints the closure size
```

Comparator was not run: the upstream README says it needs about 64 GB of memory, and the measuring machine had 15 GB.

## Ledger

`LEDGER.md` is append only, one dated entry per cut.
