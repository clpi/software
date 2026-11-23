import SoftwareDoesntRegress.Gate

set_option autoImplicit false

namespace SoftwareDoesntRegress.Audit.Readings

open SoftwareIsQuantifiable.Pareto

/-- In the subset reading, the arguments to `behaviorsKept` are reversed:
    every candidate behavior is old. The empty candidate loses the sole
    required capability while passing that reading. -/
theorem subset_deletes_only_requirement :
    behaviorsKept ([] : List Nat) [0] = true ∧
      behaviorsKept [0] ([] : List Nat) = false := by
  decide

/-- One new capability is enough for subset-to-old to refuse a feature. -/
theorem subset_refuses_feature_addition :
    behaviorsKept [0, 1] ([0] : List Nat) = false ∧
      behaviorsKept [0] ([0, 1] : List Nat) = true := by
  decide

/-- With an empty baseline, one behavior is the absolute minimum. -/
theorem subset_refuses_first_feature :
    behaviorsKept [0] ([] : List Nat) = false ∧
      behaviorsKept ([] : List Nat) [0] = true := by
  decide

/-- The actual upstream release checker retains qualification, context, and
    costs, but has no allowed-behavior argument. Here 1 is forbidden by [0]. -/
theorem qualified_release_can_add_forbidden_behavior :
    acceptsRelease () ()
      ({ qualified := [0] } : PriorQualification Nat)
      { offered := [0, 1] } (0, 0) (0, 0) = true ∧
      (1 : Nat) ∈ [0, 1] ∧ (1 : Nat) ∉ [0] := by
  decide

/-- If qualification is empty, even one newly forbidden behavior suffices. -/
theorem empty_qualification_admits_one_forbidden_behavior :
    acceptsRelease () ()
      ({ qualified := [] } : PriorQualification Nat)
      { offered := [0] } (0, 0) (0, 0) = true ∧
      (0 : Nat) ∉ [] := by
  decide

/-- The repository's existing strict gate even counts forbidden novelty as
    a strict gain, when supplied only these behavior and cost projections. -/
theorem target_gate_counts_forbidden_novelty_as_gain :
    let inc : SoftwareDoesntRegress.Profile Nat :=
      { behaviors := [0], bounds := [{ lo := 0, hi := 0 }] }
    let cand : SoftwareDoesntRegress.Profile Nat :=
      { behaviors := [0, 1], bounds := [{ lo := 0, hi := 0 }] }
    accepts [inc] [cand] = true ∧ profileStrict inc cand = true ∧
      (1 : Nat) ∉ [0] := by
  decide

/-- When qualification is all old behavior and the upper envelope is the
    old behavior too, the two inclusions force extensional equality. -/
theorem frozen_sandwich_is_membership_equality
    {B : Type} [DecidableEq B] {old cand : List B}
    (hrequired : behaviorsKept old cand = true)
    (hallowed : behaviorsKept cand old = true) :
    ∀ b, b ∈ old ↔ b ∈ cand := by
  intro b
  exact ⟨(behaviorsKept_iff old cand).mp hrequired b,
    (behaviorsKept_iff cand old).mp hallowed b⟩

/-- The fourth reading, cost non-regression alone, can reward shutdown. -/
theorem cost_only_reading_accepts_capability_deletion :
    noWorse (0, 0) (1, 0) ∧ behaviorsKept [0] ([] : List Nat) = false := by
  decide

/-- An improved positive weighted score can still worsen a protected axis. -/
theorem scalar_score_improvement_can_regress :
    weight2 1 1 (1, 0) < weight2 1 1 (0, 2) ∧
      ¬ noWorse (1, 0) (0, 2) := by
  decide

/-- Admission below a fixed budget compares neither release to its actual
    predecessor. Both fit the budget while the second is strictly worse. -/
theorem fixed_budget_admits_regressing_pair :
    noWorse (0, 0) (1, 0) ∧ noWorse (1, 0) (1, 0) ∧
      dominates (0, 0) (1, 0) ∧ ¬ noWorse (1, 0) (0, 0) := by
  decide

/-- With the incumbent present, two axes suffice for an admitted frontier
    trade-off to worsen a protected coordinate. -/
theorem nondominated_tradeoff_regresses :
    (1, 0) ∈ frontier [(0, 1), (1, 0)] ∧
      ¬ noWorse (1, 0) (0, 1) := by
  decide

/-- On one totally ordered cost axis, incumbent non-domination already
    implies no worsening. The trade-off counterexample needs two axes. -/
theorem one_axis_nondomination_is_no_worse (old cand : Nat) :
    ¬ old < cand ↔ cand ≤ old := by
  omega

/-- Omitting the incumbent lets even a one-varying-axis loser be a frontier. -/
theorem own_candidate_frontier_can_be_worse :
    (1, 0) ∈ frontier [(1, 0)] ∧ dominates (0, 0) (1, 0) := by
  decide

/-- Adjacent non-domination has no sequence theorem: each step passes,
    but the first release dominates the last. -/
theorem adjacent_nondomination_is_not_transitive :
    ¬ dominates (0, 1) (1, 0) ∧
      ¬ dominates (1, 0) (0, 2) ∧ dominates (0, 1) (0, 2) := by
  decide

/-- Even a two-release trade-off can be traversed in both directions. -/
theorem adjacent_nondomination_allows_return :
    ¬ dominates (0, 1) (1, 0) ∧ ¬ dominates (1, 0) (0, 1) ∧
      (0, 1) ≠ ((1, 0) : Point) := by
  decide

/-- Covering every previous option says an acceptable option is available;
    it says nothing about selecting a different, regressing option. -/
theorem frontier_coverage_does_not_protect_deployed_choice :
    (∀ old ∈ ([(0, 1)] : List Point),
      ∃ cand ∈ frontier [(0, 1), (1, 0)], noWorse cand old) ∧
      (1, 0) ∈ frontier [(0, 1), (1, 0)] ∧
      ¬ noWorse (1, 0) (0, 1) := by
  refine ⟨?_, by decide⟩
  intro old hold
  simp only [List.mem_singleton] at hold
  subst old
  exact ⟨(0, 1), by decide, by decide⟩

/-- A distinct candidate for each axis is not one candidate meeting all axes. -/
theorem crossed_axis_witnesses_do_not_form_replacement :
    (∃ p ∈ ([(0, 2), (2, 0)] : List Point), p.1 ≤ 1) ∧
      (∃ p ∈ ([(0, 2), (2, 0)] : List Point), p.2 ≤ 1) ∧
      ¬ ∃ p ∈ ([(0, 2), (2, 0)] : List Point), noWorse p (1, 1) := by
  simp [noWorse]

/-- Frozen qualification does not automatically protect a newly promised
    feature. Qualification must accumulate those promises between releases. -/
theorem fixed_qualification_can_lose_new_promise :
    noQualifiedBehaviorLost
      ({ qualified := [0] } : PriorQualification Nat)
      { offered := [0, 1] } = true ∧
      noQualifiedBehaviorLost
        ({ qualified := [0] } : PriorQualification Nat)
        { offered := [0] } = true ∧
      (1 : Nat) ∈ [0, 1] ∧ (1 : Nat) ∉ [0] := by
  decide

/-- Removing an unqualified behavior passes qualified retention. Keeping
    every old observation would unnecessarily forbid this deletion. -/
theorem unqualified_removal_passes_retention :
    noQualifiedBehaviorLost
      ({ qualified := [0] } : PriorQualification Nat)
      { offered := [0] } = true ∧
      behaviorsKept [0, 1] ([0] : List Nat) = false := by
  decide

/-- If 1 was put in qualification, deleting it is correctly rejected by
    that contract. Calling 1 dead does not discharge the qualification. -/
theorem protected_artifact_removal_is_refused :
    noQualifiedBehaviorLost
      ({ qualified := [0, 1] } : PriorQualification Nat)
      { offered := [0] } = false := by
  decide

/-- The unordered event projection cannot distinguish stop-then-open from
    open-then-stop. This is a projection limit, not a limit of Lean lists. -/
theorem unordered_projection_hides_order :
    behaviorsKept [0, 1] ([1, 0] : List Nat) = true ∧
      behaviorsKept [1, 0] ([0, 1] : List Nat) = true ∧
      ([0, 1] : List Nat).head? = some 0 ∧
      ([1, 0] : List Nat).head? ≠ some 0 := by
  decide

/-- Erasing symbol identity lets a behavior move to another API while the
    projected behavior list stays unchanged. Tagged retention catches it. -/
theorem flattened_behaviors_hide_removed_symbol :
    behaviorsKept
      (([(0, 0)] : List (Nat × Nat)).map Prod.snd)
      (([(1, 0)] : List (Nat × Nat)).map Prod.snd) = true ∧
      behaviorsKept ([(0, 0)] : List (Nat × Nat)) [(1, 0)] = false := by
  decide

/-- Existing context equality correctly rejects an explicit context change;
    it cannot establish the physical truth of labels supplied by a caller. -/
theorem declared_context_change_is_refused :
    acceptsRelease (0 : Nat) 1
      ({ qualified := [0] } : PriorQualification Nat)
      { offered := [0] } (1, 1) (0, 0) = false := by
  decide

/-- Narrowing uncertainty is not identical to lowering both endpoints.
    [1,1] is contained in [0,2] and improves its upper bound, yet the
    repository's endpoint preorder refuses it because its lower bound rises. -/
theorem information_refinement_is_not_endpoint_improvement :
    Bound.noWorse { lo := 0, hi := 2 } { lo := 1, hi := 1 } = false ∧
      (0 : Nat) ≤ 1 ∧ (1 : Nat) ≤ 2 ∧ (1 : Nat) < 2 := by
  decide

end SoftwareDoesntRegress.Audit.Readings
