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
| 8 | `F = 0` from vanishing lower sums by induction, not incidence-algebra Möbius inversion | 216,723 | 112 removed, 1 added |
| 9 | `Subsingleton (Gf E n)` for empty `n` from matrices over an empty index, not via perfect and nilpotent groups | | |
| 10 | `‖p - s • q‖ ≤ 1` for orthogonal projections from the C*-identity, not the commutative C*-algebra of the pair | | |
| 11 | idempotent generator of `(a)` from a pseudo-inverse `a g a = a`, not semisimple-ring structure theory | | |
| 9-11 | all three, built together | 216,431 | 295 removed (95 / 106 / 94), 3 added |
| 12 | representation with character `χ ψ` as `Representation.tprod`, not the monoidal category of representations | | |
| 13 | Kronecker star homomorphisms written down directly, not through `Mᵣ ⊗ M_c ≃ M_(r×c)` | | |
| 14 | one lemma stops instance search going through the commutative C*-algebra of bounded functions (a detour, not an argument) | | |
| 12-14 | all three, built together | 216,233 | 199 removed (103 / 59 / 37), 1 added |
| 15 | tried: char-zero smoothness without matroids; removed nothing (perfect-field case still needed), not landed | | |
| 16 | smooth extension from a neighbourhood of a closed set by the cutoff `a / (a + b)`, not partitions of unity on manifolds | 215,968 | 266 removed, 1 added |
| 17 | local-to-global smooth map with a normed-space bump `ContDiffBump`, not manifold bump functions | 215,747 | 221 removed, 0 added |
| 18 | fixed points of the involution as a `Subfield`, not the field structure on `selfAdjoint` | | |
| 19 | finiteness of an orbit quotient passed directly (an instance detour, not an argument) | | |
| 18-19 | both, built together | 215,653 | 100 removed (62 / 38), 6 added |
| 20 | connected neighbourhood as a convex ball, not via locally path-connected spaces | | |
| 21 | lattice-valued map on a connected space constant by discreteness, not via zero-dimensional spaces | | |
| 20-21 | both, built together | 215,590 | 63 removed (38 / 25), 0 added |

Build: `lake build Main` 9,850 jobs, exit 0 (cuts 1-14, 16-21: 1,867 s). Axioms: `receipts/axioms_compact.out`. Exact constant lists: `receipts/removed_constants.txt`, `receipts/added_constants.txt`.

## Where the proof's weight is

- Declaration-level usage: `riemannHypothesis` uses 98.6% of the project's declaration lines; the five theorems together add 37 lines. There is no dead code to delete.
- Dominator tree of the closure (`tools/domfull.py`, `receipts/dominators_*.tsv`): for every constant, what leaves the closure if only that constant's proof changes. `New.exists_isRegularFamily` (the Selmer and Galois-representation family) alone carries 34.7% of the project's lines. Of the 170,159 Mathlib and core constants, 41,219 are reached through exactly one local lemma; those are the cuts this method can reach. `receipts/FRONTIER.md` ranks them.
- The regular family is used as a per-prime congruence bound on the space of lifts, per dimension and independent of the ambient dimension. Both Galois-free bounds tried (Hecke resultant, Gram determinant) lose a factor of the ambient dimension. No compact replacement found.

## Reproduce

```
git clone https://github.com/lsernau/grh-lean && cd grh-lean && git checkout 72fead102f663d5c
git apply ../software/grh-compact/cuts-1-2.patch ../software/grh-compact/cut-3.patch ../software/grh-compact/cut-4.patch ../software/grh-compact/cut-5.patch ../software/grh-compact/cut-6.patch ../software/grh-compact/cut-7.patch ../software/grh-compact/cut-8.patch ../software/grh-compact/cut-9.patch ../software/grh-compact/cut-10.patch ../software/grh-compact/cut-11.patch ../software/grh-compact/cut-12.patch ../software/grh-compact/cut-13.patch ../software/grh-compact/cut-14.patch ../software/grh-compact/cut-16.patch ../software/grh-compact/cut-17.patch ../software/grh-compact/cut-18.patch ../software/grh-compact/cut-19.patch ../software/grh-compact/cut-20.patch ../software/grh-compact/cut-21.patch
cd grh && lake build Main
lake env lean ../../software/grh-compact/tools/Axioms.lean
lake env lean ../../software/grh-compact/tools/MainEdgesFull.lean   # writes edges_full.tsv, prints the closure size
```

Comparator was not run: the upstream README says it needs about 64 GB of memory, and the measuring machine had 15 GB.

## Ledger

`LEDGER.md` is append only, one dated entry per cut.
