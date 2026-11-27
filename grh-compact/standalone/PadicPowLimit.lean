import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Dvd

open Filter Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- In an ultrametric field, `‖w ^ m - 1‖ ≤ ‖w - 1‖` once `‖w - 1‖ < 1`. -/
lemma New.padic_norm_pow_sub_one_le {w : ℂ_[p]} (hw : ‖w - 1‖ < 1) (m : ℕ) :
    ‖w ^ m - 1‖ ≤ ‖w - 1‖ := by
  have hw1 : ‖w‖ = 1 := by
    have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := w - 1) (y := 1)
      (by simpa using hw.ne)
    simpa [hw.le] using h
  have hgeom : ‖∑ i ∈ range m, w ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ by
      simp [norm_pow, hw1]
  calc ‖w ^ m - 1‖ = ‖(∑ i ∈ range m, w ^ i) * (w - 1)‖ := by rw [geom_sum_mul]
    _ ≤ 1 * ‖w - 1‖ := by rw [norm_mul]; gcongr
    _ = ‖w - 1‖ := one_mul _

/-- One `p`-th power step: `‖w ^ p - 1‖ ≤ max ‖p‖ ‖w - 1‖ ^ (p - 1) · ‖w - 1‖`. -/
lemma New.padic_norm_pow_prime_sub_one_le {w : ℂ_[p]} (hw : ‖w - 1‖ < 1) :
    ‖w ^ p - 1‖ ≤ max ‖(p : ℂ_[p])‖ (‖w - 1‖ ^ (p - 1)) * ‖w - 1‖ := by
  set t := w - 1
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have h_exp : w ^ p - 1 = ∑ k ∈ range p, (p.choose (k + 1) : ℂ_[p]) * t ^ (k + 1) := by
    have h := add_pow t 1 p
    simp only [one_pow, mul_one] at h
    rw [show w = t + 1 by ring, h, sum_range_succ' _ p]
    simp [mul_comm]
  rw [h_exp]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk ↦ ?_
  have hk : k < p := mem_range.1 hk
  rw [norm_mul, norm_pow]
  have ht1 : ‖t‖ ≤ 1 := hw.le
  rcases Nat.lt_or_ge (k + 1) p with hlt | hge
  · -- `p` divides the binomial coefficient
    obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self hp.out (Nat.succ_ne_zero k) hlt
    have hc' : ‖(p.choose (k + 1) : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ := by
      rw [hc, Nat.cast_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ c)
    calc ‖(p.choose (k + 1) : ℂ_[p])‖ * ‖t‖ ^ (k + 1)
        ≤ ‖(p : ℂ_[p])‖ * ‖t‖ := by
          gcongr
          exact pow_le_of_le_one (norm_nonneg _) ht1 (Nat.succ_ne_zero k)
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hk' : k + 1 = p := by omega
    rw [hk', Nat.choose_self, Nat.cast_one, norm_one, one_mul]
    calc ‖t‖ ^ p = ‖t‖ ^ (p - 1) * ‖t‖ := by rw [← pow_succ, Nat.sub_add_cancel hp1]
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- `u ^ q ^ n → 1` when `‖u - 1‖ < 1` and `p ∣ q`, by iterating the `p`-th power step. -/
lemma New.padic_tendsto_pow_pow_of_norm_sub_one_lt {u : ℂ_[p]} (hu : ‖u - 1‖ < 1) {q : ℕ}
    (hq : p ∣ q) : Tendsto (fun n : ℕ ↦ u ^ q ^ n) atTop (nhds 1) := by
  obtain ⟨s, rfl⟩ := hq
  set c := max ‖(p : ℂ_[p])‖ (‖u - 1‖ ^ (p - 1))
  have hc0 : 0 ≤ c := le_max_of_le_left (norm_nonneg _)
  have hc1 : c < 1 := by
    have hpn : ‖(p : ℂ_[p])‖ < 1 := by
      have h := (Padic.norm_natCast_lt_one_iff (p := p)).2 (dvd_refl p)
      rwa [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap']
    refine max_lt hpn ?_
    exact pow_lt_one₀ (norm_nonneg _) hu (by have := hp.out.two_le; omega)
  -- `‖u ^ p ^ n - 1‖ ≤ c ^ n ‖u - 1‖`
  have h_step : ∀ n : ℕ, ‖u ^ p ^ n - 1‖ ≤ c ^ n * ‖u - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hle : ‖u ^ p ^ n - 1‖ ≤ ‖u - 1‖ := New.padic_norm_pow_sub_one_le hu _
      have hlt : ‖u ^ p ^ n - 1‖ < 1 := hle.trans_lt hu
      calc ‖u ^ p ^ (n + 1) - 1‖ = ‖(u ^ p ^ n) ^ p - 1‖ := by rw [pow_succ, pow_mul]
        _ ≤ max ‖(p : ℂ_[p])‖ (‖u ^ p ^ n - 1‖ ^ (p - 1)) * ‖u ^ p ^ n - 1‖ :=
          New.padic_norm_pow_prime_sub_one_le hlt
        _ ≤ c * (c ^ n * ‖u - 1‖) := by
          gcongr
          exact max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hle _)
        _ = c ^ (n + 1) * ‖u - 1‖ := by ring
  have h_bound : ∀ n : ℕ, ‖u ^ (p * s) ^ n - 1‖ ≤ c ^ n * ‖u - 1‖ := fun n ↦ by
    have hlt : ‖u ^ p ^ n - 1‖ < 1 := (New.padic_norm_pow_sub_one_le hu _).trans_lt hu
    calc ‖u ^ (p * s) ^ n - 1‖ = ‖(u ^ p ^ n) ^ s ^ n - 1‖ := by rw [mul_pow, pow_mul]
      _ ≤ ‖u ^ p ^ n - 1‖ := New.padic_norm_pow_sub_one_le hlt _
      _ ≤ _ := h_step n
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) h_bound ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const ‖u - 1‖
