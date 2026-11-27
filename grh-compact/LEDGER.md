# grh-compact ledger (append only)

## 2026-11-27 cuts 1 and 2
- Cut 1: `New.exists_eigenvector_of_commute` (Lib/General/LinearAlgebra/Eigenvalues.lean) re-proved without Lie algebras. New helper `New.exists_eigenvector_of_le_iInf_maxGenEigenspace`. Standalone check `standalone/EigenNoLie.lean`.
- Cut 2: `New.exists_div_of_norm_eq_one_elem` (Lib/ClassField/GaloisCohomology/TateIndexFormula.lean) replaces Mathlib `groupCohomology.exists_div_of_norm_eq_one` at its one use. Standalone check `standalone/Hilbert90Elem.lean`.
- Full build exit 0 (9,850 jobs, 3,630 s). Axioms unchanged for all five theorems. Closure 219,974 -> 217,911.
- Predicted by the dominator tree: 764 + 1,344 = 2,108 removed. Measured: 2,070 removed, 7 added.

## 2026-11-27 cut 3
- `card_freeEntry_level` (New/Spanning/Unfolding/ReducedGroups.lean) counted the pairs `a < b` in `Fin r` with Mathlib `Fintype.card_product_filter_lt`. Replaced by `New.sum_sum_ite_lt_fin`: count row by row with `Fin.card_Ioi`, then Gauss's sum. Patch `cut-3.patch`, standalone `standalone/PairsLt.lean`.
- Dominator-tree prediction: 98 constants removed. Measured together with cut 4 below.

## 2026-11-27 cut 4, and the measured build for cuts 3-4
- `New.tendsto_pow_pow_of_norm_sub_one_lt` (Lib/General/NumberTheory/PadicLimitsValuation.lean) used continuous additive characters of `ℤ_p` (Mahler series). Replaced by an ultrametric estimate: `‖w^p - 1‖ ≤ max ‖p‖ ‖w-1‖^(p-1) · ‖w-1‖`, iterated. New helpers `New.padic_norm_pow_sub_one_le`, `New.padic_norm_pow_prime_sub_one_le`. Patch `cut-4.patch`, standalone `standalone/PadicPowLimit.lean`.
- Build of cuts 1-4 together: `lake build Main` 9,850 jobs, exit 0, 1,263 s. Axioms for all five theorems unchanged (`receipts/cuts-3-4_axioms.out`).
- Closure 217,911 -> 217,742 (-169): 175 removed, exactly the dominator-tree prediction (98 + 77), 6 added. Lists: `receipts/cuts-3-4_removed.txt`, `receipts/cuts-3-4_added.txt`.
