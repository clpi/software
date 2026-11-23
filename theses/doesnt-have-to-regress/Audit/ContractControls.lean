import Audit.Contract

set_option autoImplicit false

namespace SoftwareDoesntRegress.Audit.ContractControls

open SoftwareIsQuantifiable.Pareto

def contract : Contract Nat Nat Unit Nat where
  context := 0
  keys := [()]
  prior _ := { qualified := [0] }
  allowed _ := [0, 1]

def release (offered possible : List Nat) (cost : Point) (context : Nat := 0) :
    ScopedRelease Nat Nat Unit Nat where
  context := context
  profile _ := { offered := { offered := offered }, possible := possible, cost := cost }

def baseline : ScopedRelease Nat Nat Unit Nat := release [0] [0] (1, 1)

def feature : ScopedRelease Nat Nat Unit Nat := release [0, 1] [0, 1] (1, 1)

/-- Required capability retention is necessary even with allowed outcomes,
    unchanged context, and improved cost. -/
theorem capability_conjunct_rejects_deletion :
    let candidate := release [] [0] (0, 0)
    permitted contract candidate () = true ∧
      compareCosts contract baseline candidate = true ∧
      candidate.context = baseline.context ∧
      replacement contract baseline candidate = false := by
  decide

/-- The allowed-outcome conjunct rejects the previously demonstrated hole
    in upstream qualified-retention plus cost admission. -/
theorem envelope_conjunct_rejects_forbidden_novelty :
    let candidate := release [0] [0, 2] (1, 1)
    acceptsRelease baseline.context candidate.context (contract.prior ())
      (candidate.profile ()).offered (baseline.profile ()).cost
      (candidate.profile ()).cost = true ∧
      permitted contract candidate () = false ∧
      replacement contract baseline candidate = false := by
  decide

/-- A newly disallowed effect cannot hide behind a strictly better cost. -/
theorem cost_improvement_cannot_pay_for_forbidden_outcome :
    let candidate := release [0] [2] (0, 0)
    dominates (candidate.profile ()).cost (baseline.profile ()).cost ∧
      replacement contract baseline candidate = false := by
  decide

/-- Safety and required capabilities alone do not prevent metric regression. -/
theorem cost_conjunct_rejects_slowdown :
    let candidate := release [0] [0] (2, 1)
    certified contract baseline = true ∧ certified contract candidate = true ∧
      compareCosts contract baseline candidate = false ∧
      replacement contract baseline candidate = false := by
  decide

/-- A context mismatch is rejected even when all other projected data agree. -/
theorem context_conjunct_rejects_changed_scope :
    let candidate := release [0] [0] (1, 1) 1
    permitted contract candidate () = true ∧
      noQualifiedBehaviorLost (contract.prior ()) (candidate.profile ()).offered = true ∧
      compareCosts contract baseline candidate = true ∧
      replacement contract baseline candidate = false := by
  decide

/-- Feature addition is permitted when it preserves qualification, stays in
    the approved outcome envelope, and worsens neither protected cost axis. -/
theorem approved_optional_feature_is_admitted :
    replacement contract baseline feature = true := by
  decide

/-- The same frozen contract permits removing an optional feature. This
    describes optionality, not permission to erase a recorded promise. -/
theorem unpromised_optional_feature_is_removable :
    replacement contract feature baseline = true := by
  decide

/-- The baseline does not already have a feature merely because it was
    added to a future contract. Promise recording follows feature admission. -/
theorem promise_recording_requires_current_support :
    certified (recordPromises contract (fun _ => [1])) baseline = false ∧
      certified (recordPromises contract (fun _ => [1])) feature = true := by
  decide

/-- Once the feature is promised, the former baseline is no longer an
    admissible replacement and fail-closed shipping retains the feature. -/
theorem recorded_promise_prevents_feature_loss :
    let promised := recordPromises contract (fun _ => [1])
    replacement promised feature baseline = false ∧
      (ship promised feature baseline).profile () = feature.profile () := by
  exact ⟨by decide, rfl⟩

/-- Removing an unrequired possible outcome is valid; retaining every old
    possible outcome would wrongly prevent this safety improvement. -/
theorem optional_possible_outcome_can_disappear :
    replacement contract (release [0] [0, 1] (1, 1)) baseline = true := by
  decide

/-- A fallback is safe only if the baseline was certified. This deliberately
    violates that precondition and shows fallback can preserve invalidity. -/
theorem invalid_baseline_is_not_repaired_by_fallback :
    let invalid := release [] [2] (1, 1)
    certified contract invalid = false ∧
      replacement contract invalid baseline = false ∧
      certified contract (ship contract invalid baseline) = false := by
  decide

/-- The public deployment wrapper refuses to publish any result when the
    baseline has not passed the contract. No validity premise is hidden. -/
theorem invalid_baseline_emits_no_deployment :
    let invalid := release [] [2] (1, 1)
    certified contract invalid = false ∧
      deploy contract invalid baseline = none := by
  exact ⟨by decide, rfl⟩

/-- With a certified baseline, an invalid candidate produces that baseline
    as the published result rather than publishing the invalid candidate. -/
theorem invalid_candidate_retains_certified_baseline :
    deploy contract baseline (release [] [2] (0, 0)) = some baseline := by
  rfl

/-- Even an empty list of protected keys does not bypass context equality. -/
theorem empty_scope_still_checks_context :
    let empty := { contract with keys := [] }
    certified empty (release [] [2] (2, 2) 1) = false := by
  decide

/-- An empty declared scope protects no behaviors or costs. A meaningful
    application must justify the protected-key coverage separately. -/
theorem empty_scope_is_vacuous_inside_matching_context :
    let empty := { contract with keys := [] }
    replacement empty baseline (release [] [2] (2, 2)) = true := by
  decide

/-- Declared capability membership and declared possible outcomes have no
    built-in execution relation. Model fidelity is an application premise. -/
theorem declared_capability_does_not_establish_execution :
    let projection := release [0] [] (0, 0)
    certified contract projection = true ∧
      replacement contract baseline projection = true ∧
      (projection.profile ()).possible = [] := by
  decide

def keyedContract : Contract Nat Nat Bool Nat where
  context := 0
  keys := [false]
  prior _ := { qualified := [0] }
  allowed _ := [0]

def originalKeyed : ScopedRelease Nat Nat Bool Nat where
  context := 0
  profile k :=
    if k then { offered := { offered := [] }, possible := [], cost := (1, 1) }
    else { offered := { offered := [0] }, possible := [0], cost := (1, 1) }

def movedKeyed : ScopedRelease Nat Nat Bool Nat where
  context := 0
  profile k :=
    if k then { offered := { offered := [0] }, possible := [0], cost := (1, 1) }
    else { offered := { offered := [] }, possible := [], cost := (1, 1) }

/-- Moving a capability to another key cannot satisfy the old API contract. -/
theorem key_identity_rejects_moved_capability :
    certified keyedContract originalKeyed = true ∧
      certified keyedContract movedKeyed = false ∧
      replacement keyedContract originalKeyed movedKeyed = false := by
  decide

end SoftwareDoesntRegress.Audit.ContractControls
