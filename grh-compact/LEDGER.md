# grh-compact ledger (append only)

## 2026-11-27 cuts 1 and 2
- Cut 1: `New.exists_eigenvector_of_commute` (Lib/General/LinearAlgebra/Eigenvalues.lean) re-proved without Lie algebras. New helper `New.exists_eigenvector_of_le_iInf_maxGenEigenspace`. Standalone check `standalone/EigenNoLie.lean`.
- Cut 2: `New.exists_div_of_norm_eq_one_elem` (Lib/ClassField/GaloisCohomology/TateIndexFormula.lean) replaces Mathlib `groupCohomology.exists_div_of_norm_eq_one` at its one use. Standalone check `standalone/Hilbert90Elem.lean`.
- Full build exit 0 (9,850 jobs, 3,630 s). Axioms unchanged for all five theorems. Closure 219,974 -> 217,911.
- Predicted by the dominator tree: 764 + 1,344 = 2,108 removed. Measured: 2,070 removed, 7 added.

## 2026-11-27 cut 3
- `card_freeEntry_level` (New/Spanning/Unfolding/ReducedGroups.lean) counted the pairs `a < b` in `Fin r` with Mathlib `Fintype.card_product_filter_lt`. Replaced by `New.sum_sum_ite_lt_fin`: count row by row with `Fin.card_Ioi`, then Gauss's sum. Patch `cut-3.patch`, standalone `standalone/PairsLt.lean`.
- Dominator-tree prediction: 98 constants removed. Measured together with cut 4 below.
