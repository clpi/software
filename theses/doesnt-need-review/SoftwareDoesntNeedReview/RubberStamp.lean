import SoftwareDoesntNeedReview.Reviewer
import SoftwareDoesntNeedReview.Chain

namespace SoftwareDoesntNeedReview

namespace RubberStamp

theorem verdict_constant (C : Certifier) (base : Release) (r : Reviewer)
    (R1 R2 : Release) (f : Facts) (hr : FactorsThrough r)
    (h1 : factsOf C R1 = f) (h2 : factsOf C R2 = f) :
    r (sightOf C base R1) = r (sightOf C base R2) := by
  apply hr
  simp [sightOf, h1, h2]

theorem zero_information (C : Certifier) (r : Reviewer) (base : Release) (f : Facts)
    (R0 : Release) (bit : Bool) (hr : FactorsThrough r) (h0 : factsOf C R0 = f)
    (hbit : r (sightOf C base R0) = bit) :
    ∀ R, (factsOf C R = f ∧ r (sightOf C base R) = bit) ↔ factsOf C R = f := by
  intro R
  constructor
  · intro h
    exact h.1
  · intro hR
    exact ⟨hR, (verdict_constant C base r R R0 f hr hR h0).trans hbit⟩

theorem veto_empties (C : Certifier) (r : Reviewer) (base : Release) (f : Facts)
    (R0 : Release) (hr : FactorsThrough r) (h0 : factsOf C R0 = f)
    (hbit : r (sightOf C base R0) = false) :
    ∀ R, ¬ (factsOf C R = f ∧ r (sightOf C base R) = true) := by
  intro R ⟨hR, hrR⟩
  have hv := verdict_constant C base r R R0 f hr hR h0
  rw [hrR, hbit] at hv
  cases hv

theorem agrees_or_pure_veto (C : Certifier) (r : Reviewer) (base : Release) (f : Facts)
    (R0 : Release) (hr : FactorsThrough r) (hs : Respects r C base)
    (h0 : factsOf C R0 = f) :
    (∀ R, factsOf C R = f → r (sightOf C base R) = certBit f) ∨
      (certBit f = true ∧ ∀ R, factsOf C R = f → r (sightOf C base R) = false) := by
  cases hbit : r (sightOf C base R0)
  · cases hcert : certBit f
    · left
      intro R hR
      have hv := verdict_constant C base r R R0 f hr hR h0
      rw [hbit] at hv
      simpa [hcert] using hv.symm
    · right
      refine ⟨rfl, ?_⟩
      have _used : certBit f = true := hcert
      intro R hR
      have hv := verdict_constant C base r R R0 f hr hR h0
      simpa [hbit] using hv
  · left
    have hempty : f.refusals = [] := by
      have h := hs R0 hbit
      simpa [h0] using h
    have hcert : certBit f = true := by simp [certBit, hempty]
    intro R hR
    have hv := verdict_constant C base r R R0 f hr hR h0
    rw [hbit] at hv
    simpa [hcert] using hv.symm

theorem alwaysReject_factors : FactorsThrough alwaysReject := by
  intro _ _ _
  rfl

theorem alwaysReject_respects (C : Certifier) (base : Release) :
    Respects alwaysReject C base := by
  intro _ h
  simp [alwaysReject] at h

theorem constant_reject_is_veto (C : Certifier) (base : Release) (f : Facts) (R0 : Release)
    (h0 : factsOf C R0 = f) (hempty : f.refusals = []) :
    FactorsThrough alwaysReject ∧ Respects alwaysReject C base ∧
      (factsOf C R0).refusals = [] ∧ certBit f = true ∧
        ∀ R, factsOf C R = f → alwaysReject (sightOf C base R) = false := by
  refine ⟨alwaysReject_factors, alwaysReject_respects C base, ?_, ?_, ?_⟩
  · simpa [h0] using hempty
  · simp [certBit, hempty]
  · intro _ _
    rfl

theorem alwaysApprove_factors : FactorsThrough alwaysApprove := by
  intro _ _ _
  rfl

theorem guarded_independent_of_approval (approve : Bool) (cand inc : Nat × Nat)
    (h : Chain.Optimality.noWorse cand inc) :
    (approve = true ∨ approve = false) ∧
      Chain.Optimality.acceptsGuarded true false cand inc := by
  cases approve with
  | false => exact ⟨Or.inr rfl, rfl, rfl, h⟩
  | true => exact ⟨Or.inl rfl, rfl, rfl, h⟩

end RubberStamp

end SoftwareDoesntNeedReview
