import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

open Finset

/-- Hilbert 90 for a finite cyclic Galois extension, by Dedekind's independence of characters and
no group cohomology: if `g` generates `Gal(L/K)` and `N_{L/K}(x) = 1` then `x = y / g y`. -/
theorem exists_div_of_norm_eq_one_elem {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {g : Gal(L/K)} (hg : ∀ σ, σ ∈ Subgroup.zpowers g)
    {x : L} (hx : Algebra.norm K x = 1) : ∃ y : Lˣ, y / g y = x := by
  classical
  set n := orderOf g with hn_def
  have hn_card : n = Fintype.card Gal(L/K) := by
    rw [hn_def, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hn_pos : 0 < n := orderOf_pos g
  -- the powers `g ^ i`, `i < n`, enumerate the Galois group
  let e : Fin n → Gal(L/K) := fun i ↦ g ^ (i : ℕ)
  have he_inj : Function.Injective e := fun i j h ↦
    Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.2 i.2) (Set.mem_Iio.2 j.2) h)
  have he_bij : Function.Bijective e :=
    (Fintype.bijective_iff_injective_and_card e).2 ⟨he_inj, by simp [hn_card]⟩
  -- partial norms `p i = x · g x ⋯ g^(i-1) x`
  let p : ℕ → L := fun i ↦ ∏ j ∈ range i, (g ^ j) x
  have hp_n : p n = 1 := by
    have h := Algebra.norm_eq_prod_automorphisms K x
    rw [hx, map_one, ← Fintype.prod_bijective e he_bij (fun i ↦ (g ^ (i : ℕ)) x) (fun σ ↦ σ x)
      (fun _ ↦ rfl), Fin.prod_univ_eq_prod_range (fun i ↦ (g ^ i) x)] at h
    exact h.symm
  have hp_succ (i : ℕ) : x * g (p i) = p (i + 1) := by
    simp only [p, map_prod, prod_range_succ', pow_zero, AlgEquiv.one_apply]
    rw [mul_comm]
    congr 1
    refine prod_congr rfl fun j _ ↦ ?_
    rw [pow_succ', AlgEquiv.mul_apply]
  -- Dedekind: the combination `∑ p i · g^i` of distinct automorphisms is not zero
  obtain ⟨c, hc⟩ : ∃ c : L, ∑ i ∈ range n, p i * (g ^ i) c ≠ 0 := by
    by_contra! h
    let v : Fin n → (L →* L) := fun i ↦ ((e i : L ≃ₐ[K] L) : L →* L)
    have hv_inj : Function.Injective v := fun i j hij ↦ he_inj (AlgEquiv.ext fun y ↦
      DFunLike.congr_fun hij y)
    have h_li := (linearIndependent_monoidHom L L).comp v hv_inj
    have h0 := Fintype.linearIndependent_iff.1 h_li (fun i ↦ p i) (funext fun c ↦ by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, v, e,
        Pi.zero_apply]
      exact (Fin.sum_univ_eq_sum_range (fun i ↦ p i * (g ^ i) c) n).trans (h c)) ⟨0, hn_pos⟩
    simp [p] at h0
  set b := ∑ i ∈ range n, p i * (g ^ i) c
  have hgb : x * g b = b := by
    have hshift : ∑ i ∈ range n, p (i + 1) * (g ^ (i + 1)) c = ∑ i ∈ range n, p i * (g ^ i) c := by
      have h1 := sum_range_succ (fun i ↦ p i * (g ^ i) c) n
      have h2 := sum_range_succ' (fun i ↦ p i * (g ^ i) c) n
      rw [hp_n, pow_orderOf_eq_one, one_mul, AlgEquiv.one_apply] at h1
      simp only [p, range_zero, prod_empty, pow_zero, AlgEquiv.one_apply, one_mul] at h2
      linear_combination h2.symm.trans h1
    simp only [b, map_sum, map_mul, mul_sum]
    rw [← hshift]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← mul_assoc, hp_succ, pow_succ', AlgEquiv.mul_apply]
  have hgb0 : g b ≠ 0 := (map_ne_zero g).2 hc
  refine ⟨Units.mk0 b hc, ?_⟩
  rw [Units.val_mk0, div_eq_iff hgb0]
  exact hgb.symm
