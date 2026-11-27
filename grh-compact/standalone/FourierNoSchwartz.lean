import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2

section NonstationaryPhase

open Complex Real FourierTransform ContDiff MeasureTheory

/-- For a vector `b` of a real inner product space and `v = ‖b‖⁻¹ • b` (which is `0` if `b = 0`),
the number `i + 2 π i ⟪b, v⟫` has norm at least `1 + ‖b‖`: its imaginary part is `1 + 2 π ‖b‖`. -/
lemma New.one_add_norm_le_norm_I_add_inner {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : V) :
    1 + ‖b‖ ≤ ‖(Complex.I + 2 * π * Complex.I * inner ℝ b (‖b‖⁻¹ • b) : ℂ)‖ := by
  have h_inner : inner ℝ b (‖b‖⁻¹ • b) = ‖b‖ := by simp [inner_smul_right, field, sq]
  calc 1 + ‖b‖
    _ ≤ 1 + 2 * π * ‖b‖ := by nlinarith [norm_nonneg b, two_le_pi]
    _ = (Complex.I + 2 * π * Complex.I * inner ℝ b (‖b‖⁻¹ • b) : ℂ).im := by simp [h_inner]
    _ ≤ _ := im_le_norm _

/-- The product rule for the derivative of `g * exp (h / a)` in the direction `v`. -/
lemma fderiv_mul_exp_div_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g h : E → ℂ} {x : E} (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (a : ℂ)
    (v : E) :
    fderiv ℝ (fun y : E ↦ g y * Complex.exp (h y / a)) x v =
      fderiv ℝ g x v * Complex.exp (h x / a) +
        g x * (Complex.exp (h x / a) * (fderiv ℝ h x v / a)) := by
  simp only [div_eq_mul_inv]
  rw [(hg.hasFDerivAt.fun_mul (hh.hasFDerivAt.mul_const a⁻¹).cexp).fderiv]
  simp [add_comm, mul_comm]

/-- Let `c` and `q` be smooth functions of a parameter `s : T` and a point `x : ℂ^n`, with
`c (s, x) = 0` for `x` off the compact set `K`. For each `M` there is a `C` such that, for
`‖s‖ ≤ 1`, `‖a‖ ≤ 1`, `a ≠ 0` and every bound `D` of `‖exp (q (s, ·) / a)‖` on `K`, the Fourier
transform of `c (s, ·) * exp (q (s, ·) / a)` at any `b`, times `(‖a‖ * (1 + ‖b‖)) ^ M`, has norm at
most `C * D`. Proof: induction on `M`, for all parameter spaces `T`. One integration by parts in the
direction `v` of `b` gives a function of the same kind, with `v` and `a` as further parameters. -/
lemma New.exists_pow_mul_norm_fourier_le {n T : Type} [Fintype n] [NormedAddCommGroup T]
    [NormedSpace ℝ T] [ProperSpace T] {K : Set (EuclideanSpace ℂ n)} (hK : IsCompact K) (M : ℕ)
    {c q : T × EuclideanSpace ℂ n → ℂ} (hc : ContDiff ℝ ∞ c) (hq : ContDiff ℝ ∞ q)
    (h_zero : ∀ (s : T) (x : EuclideanSpace ℂ n), x ∉ K → c (s, x) = 0) :
    ∃ C : ℝ, ∀ (b : EuclideanSpace ℂ n) (s : T) (a : ℂ) (D : ℝ), ‖s‖ ≤ 1 → ‖a‖ ≤ 1 → a ≠ 0 →
      (∀ x ∈ K, ‖Complex.exp (q (s, x) / a)‖ ≤ D) →
      (‖a‖ * (1 + ‖b‖)) ^ M *
        ‖𝓕 (fun x : EuclideanSpace ℂ n ↦ c (s, x) * Complex.exp (q (s, x) / a)) b‖ ≤ C * D := by
  induction M generalizing T with
  | zero =>
    -- Bound the integral by the supremum of the integrand times the volume of `K`.
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ p ∈ Metric.closedBall (0 : T) 1 ×ˢ K, ‖c p‖ ≤ B :=
      ((isCompact_closedBall 0 1).prod hK).exists_bound_of_continuousOn hc.continuous.continuousOn
    refine ⟨B * volume.real K, fun b s a D hs ha_le ha_ne hD ↦ ?_⟩
    have h_bound (x : EuclideanSpace ℂ n) (hx : x ∈ K) :
        ‖𝐞 (-inner ℝ x b) • (c (s, x) * (q (s, x) / a).exp)‖ ≤ B * D := by
      simpa using norm_mul_le_of_le (hB (s, x) ⟨mem_closedBall_zero_iff.2 hs, hx⟩) (hD x hx)
    rw [fourier_eq, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      fun x hx ↦ by simp [h_zero s x hx]]
    simpa [mul_right_comm] using norm_setIntegral_le_of_norm_le_const hK.measure_lt_top h_bound
  | succ M ih =>
    -- With `F = c · exp (q / a)` one has `a (I F + F' v) = c' · exp (q / a)`; the new
    -- amplitude `c'` is smooth in `x` and in the parameters `(s, v, a)`, and vanishes off `K`.
    let c' : (T × EuclideanSpace ℂ n × ℂ) × EuclideanSpace ℂ n → ℂ := fun ((s, v, a), x) ↦
      a * (I * c (s, x) + fderiv ℝ (fun y ↦ c (s, y)) x v) +
        c (s, x) * fderiv ℝ (fun y ↦ q (s, y)) x v
    have h_supp : ∀ (p : T × EuclideanSpace ℂ n × ℂ) (x : EuclideanSpace ℂ n), x ∉ K →
        c' (p, x) = 0 := fun (s, v, a) x hx ↦ by
      have h_near : (fun y ↦ c (s, y)) =ᶠ[nhds x] fun _ ↦ 0 :=
        Filter.eventuallyEq_of_mem (hK.isClosed.compl_mem_nhds hx) (h_zero s)
      simp [c', h_near.fderiv_eq, h_zero s x hx]
    obtain ⟨C, hC⟩ :=
      ih (c := c') (q := fun ((s, _), x) ↦ q (s, x)) (by fun_prop) (by fun_prop) h_supp
    refine ⟨C, fun b s a D hs ha_le ha_ne hD ↦ ?_⟩
    let v : EuclideanSpace ℂ n := ‖b‖⁻¹ • b
    -- `G = c · exp (q / a)` is smooth with compact support, so its Fourier transform turns the
    -- derivative in the direction `v` into multiplication by `2 π i ⟪b, v⟫`.
    let G : EuclideanSpace ℂ n → ℂ := fun x ↦ c (s, x) * (q (s, x) / a).exp
    have hG_smooth : ContDiff ℝ ∞ G := by fun_prop
    have hG_supp : HasCompactSupport G := .intro hK fun x hx ↦ by simp [G, h_zero s x hx]
    have hG_int : Integrable G := hG_smooth.continuous.integrable_of_hasCompactSupport hG_supp
    have hG_diff : Differentiable ℝ G := hG_smooth.differentiable (by simp)
    have hG'_cont : Continuous (fderiv ℝ G) := ContDiff.continuous_fderiv (𝕜 := ℝ) hG_smooth (by simp)
    have hG'_int : Integrable (fderiv ℝ G) :=
      hG'_cont.integrable_of_hasCompactSupport (hG_supp.fderiv (𝕜 := ℝ))
    have hGv_int : Integrable fun x ↦ fderiv ℝ G x v :=
      (hG'_cont.clm_apply continuous_const).integrable_of_hasCompactSupport
        ((hG_supp.fderiv (𝕜 := ℝ)).mono fun x hx h0 ↦ hx (by simp [h0]))
    have h_der : 𝓕 (fun x ↦ fderiv ℝ G x v) b = 2 * π * I * inner ℝ b v * 𝓕 G b := by
      have h := congrArg (fun T : EuclideanSpace ℂ n →L[ℝ] ℂ ↦ T v)
        (congrFun (Real.fourier_fderiv hG_int hG_diff hG'_int) b)
      have hint : Integrable fun x : EuclideanSpace ℂ n ↦ 𝐞 (-inner ℝ x b) • fderiv ℝ G x :=
        (Real.fourierIntegral_convergent_iff b).2 hG'_int
      rw [Real.fourier_eq, ContinuousLinearMap.integral_apply hint v] at h
      have h_eval (x : EuclideanSpace ℂ n) :
          (𝐞 (-inner ℝ x b) • fderiv ℝ G x) v = 𝐞 (-inner ℝ x b) • fderiv ℝ G x v := rfl
      simp only [h_eval] at h
      rw [Real.fourier_eq, h]
      simp only [VectorFourier.fourierSMulRight_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply, innerSL_apply_apply,
        neg_smul, smul_neg, neg_neg, Complex.real_smul, smul_eq_mul, Real.fourier_eq]
      rw [innerSL_apply_apply]
      ring
    have h_parts (x : EuclideanSpace ℂ n) :
        c' ((s, v, a), x) * (q (s, x) / a).exp = a * (I * G x + fderiv ℝ G x v) := by
      have hc_diff : Differentiable ℝ c := hc.differentiable (by simp)
      have hq_diff : Differentiable ℝ q := hq.differentiable (by simp)
      have h_leibniz : fderiv ℝ G x v = fderiv ℝ (fun y ↦ c (s, y)) x v * (q (s, x) / a).exp +
          c (s, x) * ((q (s, x) / a).exp * (fderiv ℝ (fun y ↦ q (s, y)) x v / a)) :=
        fderiv_mul_exp_div_apply (by fun_prop) (by fun_prop) a v
      simp only [h_leibniz, c', G]
      field
    -- On the Fourier side the operator is multiplication by `a * (I + 2 π I ⟪b, v⟫)`.
    have h_fourier :
        𝓕 (fun x ↦ a * (I * G x + fderiv ℝ G x v)) b = a * (I + 2 * π * I * inner ℝ b v) * 𝓕 G b := by
      have h_lin : 𝓕 (fun x ↦ a * (I * G x + fderiv ℝ G x v)) b =
          a * (I * 𝓕 G b + 𝓕 (fun x ↦ fderiv ℝ G x v) b) := by
        have i1 := (Real.fourierIntegral_convergent_iff b).2 hG_int
        have i2 := (Real.fourierIntegral_convergent_iff b).2 hGv_int
        simp only [Real.fourier_eq]
        calc ∫ x, 𝐞 (-inner ℝ x b) • (a * (I * G x + fderiv ℝ G x v))
            = ∫ x, a * (I * (𝐞 (-inner ℝ x b) • G x)) + a * (𝐞 (-inner ℝ x b) • fderiv ℝ G x v) := by
              congr 1; ext x; simp only [Circle.smul_def, smul_eq_mul]; ring
          _ = a * (I * ∫ x, 𝐞 (-inner ℝ x b) • G x) + a * ∫ x, 𝐞 (-inner ℝ x b) • fderiv ℝ G x v := by
              rw [integral_add ((i1.const_mul I).const_mul a) (i2.const_mul a), integral_const_mul,
                integral_const_mul, integral_const_mul]
          _ = _ := by ring
      rw [h_lin, h_der]; ring
    have h_factor : 1 + ‖b‖ ≤ ‖(I + 2 * π * I * inner ℝ b v : ℂ)‖ :=
      New.one_add_norm_le_norm_I_add_inner b
    -- So one factor `‖a‖ * (1 + ‖b‖)` is absorbed, and the induction hypothesis applies to `c'`.
    calc (‖a‖ * (1 + ‖b‖)) ^ (M + 1) * ‖𝓕 G b‖
      _ ≤ (‖a‖ * (1 + ‖b‖)) ^ M * ‖𝓕 (fun x ↦ a * (I * G x + fderiv ℝ G x v)) b‖ := by
        grw [h_fourier, norm_mul, norm_mul, ← h_factor, pow_succ, mul_assoc]
      _ ≤ C * D := by
        have h_param : ‖(s, v, a)‖ ≤ 1 := by
          simp [Prod.norm_def, hs, ha_le, v, norm_smul, inv_mul_le_one]
        rw [← funext h_parts]
        exact hC b (s, v, a) a D h_param ha_le ha_ne hD

end NonstationaryPhase
