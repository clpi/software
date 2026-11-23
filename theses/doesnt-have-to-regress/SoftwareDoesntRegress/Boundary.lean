import SoftwareDoesntRegress.Gate

namespace SoftwareDoesntRegress

theorem not_per_execution_dominance :
    ¬ ∀ x y : SoftwareIsQuantifiable.Pareto.Point,
      (1 ≤ x.1 ∧ x.1 ≤ 100 ∧ x.2 = 0) →
        (2 ≤ y.1 ∧ y.1 ≤ 3 ∧ y.2 = 0) → y.1 < x.1 :=
  SoftwareIsQuantifiable.Pareto.not_per_execution_dominance

theorem accepted_not_per_execution :
    accepts gateInc gateCand = true ∧
      ∃ x y : Nat, 10 ≤ x ∧ x ≤ 20 ∧ 8 ≤ y ∧ y ≤ 18 ∧ x < y := by
  refine ⟨?_, 10, 18, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · omega
  · omega
  · omega
  · omega
  · omega

def firstBehaviors : Release Nat → List Nat
  | [] => []
  | p :: _ => p.behaviors

theorem not_unobserved_nonregression :
    accepts observedInc observedCand = true ∧
      1 ∈ trueBehaviorsInc ∧ 1 ∉ trueBehaviorsCand ∧
      1 ∉ firstBehaviors observedInc ∧ 1 ∉ firstBehaviors observedCand := by
  decide

theorem nonregression_if_coverage {β : Type} [DecidableEq β]
    {trueBs inc cand : List β}
    (hcov : SoftwareIsQuantifiable.Pareto.noQualifiedBehaviorLost
        { qualified := trueBs } { offered := inc } = true)
    (hkeep : behaviorsKept inc cand = true) :
    SoftwareIsQuantifiable.Pareto.noQualifiedBehaviorLost
      { qualified := trueBs } { offered := cand } = true := by
  have hcov' :=
    (SoftwareIsQuantifiable.Pareto.noQualifiedBehaviorLost_iff
      (prior := { qualified := trueBs }) (submission := { offered := inc })).mp hcov
  have hkeep' := (behaviorsKept_iff inc cand).mp hkeep
  apply (SoftwareIsQuantifiable.Pareto.noQualifiedBehaviorLost_iff
      (prior := { qualified := trueBs }) (submission := { offered := cand })).mpr
  intro b hb
  exact hkeep' b (hcov' b hb)

theorem alwaysKeep_noRegress {β : Type} [DecidableEq β] (inc cand : Release β) :
    noRegress inc (alwaysKeep inc cand) = true := by
  simp [alwaysKeep, noRegress_refl]

theorem better_is_improvement : accepts baseExample betterExample = true := by
  decide

theorem not_every_gate_complete :
    ¬ ∀ gate : Release Nat → Release Nat → Release Nat,
      (∀ inc cand, noRegress inc (gate inc cand) = true) →
        ∀ inc cand, accepts inc cand = true → gate inc cand = cand := by
  intro h
  have hgate := h alwaysKeep alwaysKeep_noRegress baseExample betterExample better_is_improvement
  have hne : baseExample ≠ betterExample := by decide
  exact hne hgate

def complete_gate_decides (R : Release Nat → Release Nat → Prop)
    (gate : Release Nat → Release Nat → Bool)
    (h : ∀ inc cand, gate inc cand = true ↔ R cand inc) :
    DecidableRel R :=
  fun a b => decidable_of_iff (gate b a = true) (h b a)

theorem refuse_pure : accepts exInc exPure = false := by
  decide

theorem refuse_pure_symbol : firstRefusal exNames exInc exPure = some "emit" := by
  decide

theorem refuse_equal : accepts exInc exEqual = false := by
  decide

theorem refuse_trade : accepts exInc exTrade = false := by
  decide

theorem refuse_trade_symbol : firstRefusal exNames exInc exTrade = some "emit" := by
  decide

theorem stream_keeps_regressor : step r1 r2 = r1 := by
  decide

theorem stream_keeps_equal : step r1 r3 = r1 := by
  decide

theorem stream_ships_improvement : ascend r0 streamUniverse = r1 := by
  decide

end SoftwareDoesntRegress
