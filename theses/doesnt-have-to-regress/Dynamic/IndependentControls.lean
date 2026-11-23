import Dynamic.Engine

set_option autoImplicit false

namespace SoftwareDoesntRegress.Dynamic.IndependentControls

open SoftwareDoesntRegress.Audit
open SoftwareDoesntRegress.Dynamic
open SoftwareIsQuantifiable.Pareto

def base : Contract Nat Nat Nat Nat :=
  ⟨0, [0], fun _ => ⟨[0]⟩, fun _ => [0]⟩

def release (first second : Point) (offered : List Nat := [0])
    (context : Nat := 0) : ScopedRelease Nat Nat Nat Nat :=
  ⟨context, fun k => ⟨⟨offered⟩, [0], if k = 0 then first else second⟩⟩

def expanded : Contract Nat Nat Nat Nat := { base with keys := [0, 1] }

/- A newly protected key establishes its first baseline at admission.
   The system cannot claim a cost guarantee for a previously unprotected key. -/
theorem newly_protected_key_has_no_historical_cost_ceiling :
    let old := release (2, 2) (0, 0)
    let next := release (1, 1) (100, 100)
    Evolution.admissible ⟨base, old⟩ ⟨expanded, next⟩ = true ∧
      replacement expanded old next = false := by decide

/- After admission, that same key is protected on all later transitions. -/
theorem newly_protected_key_cannot_subsequently_regress :
    let current := release (1, 1) (100, 100)
    let next := release (0, 0) (101, 100)
    replacement base current next = true ∧
      Evolution.admissible ⟨expanded, current⟩ ⟨expanded, next⟩ = false := by decide

/- Fresh exactness for a weaker query is insufficient authority to erase
   the old contract. The integrated adoption path checks both obligations. -/
theorem exact_current_query_does_not_authorize_contract_erasure :
    let current : Engine.Artifact Nat Nat Nat Nat := ⟨1, release (1, 1) (100, 100)⟩
    (Incremental.recertify [] base current.release current.release).verdict = true ∧
      (Engine.adopt expanded base [] current current).accepted = false := by decide

def promised : Contract Nat Nat Nat Nat := recordPromises base (fun _ => [1])

/- Requiring the old release to satisfy a new promise would block the
   feature which first establishes it. The two-phase integrated path succeeds. -/
theorem integrated_adoption_establishes_new_promises :
    let old : Engine.Artifact Nat Nat Nat Nat := ⟨1, release (2, 2) (0, 0)⟩
    let next : Engine.Artifact Nat Nat Nat Nat := ⟨2, release (1, 1) (0, 0) [0, 1]⟩
    certified promised old.release = false ∧
      (Incremental.recertify [] promised old.release next.release).verdict = false ∧
      (Engine.adopt base promised [] old next).accepted = true ∧
      (Engine.adopt base promised [] old next).incumbent.id = 2 := by decide

/- Artifact labels never authorize proof reuse. Changing a context under the
   same label invalidates its exact stamps and blocks cached greedy admission. -/
theorem same_artifact_label_cannot_hide_context_change :
    let old : Engine.Artifact Nat Nat Nat Nat := ⟨1, release (2, 2) (0, 0)⟩
    let good : Engine.Artifact Nat Nat Nat Nat := ⟨2, release (1, 1) (0, 0)⟩
    let changed : Engine.Artifact Nat Nat Nat Nat := ⟨2, release (1, 1) (0, 0) [0] 1⟩
    let prior := Incremental.recertify [] base old.release good.release
    prior.verdict = true ∧
      (Engine.choose base prior.cache old changed).incumbent.id = 1 ∧
      (Engine.choose base prior.cache old changed).evaluated = 5 ∧
      Greedy.strictImproves base old.release changed.release = false := by decide

/- Reusing the former contract's successes cannot certify a new context. -/
theorem changed_contract_context_refreshes_integrated_greedy :
    let old : Engine.Artifact Nat Nat Nat Nat := ⟨1, release (2, 2) (0, 0)⟩
    let next : Engine.Artifact Nat Nat Nat Nat := ⟨2, release (1, 1) (0, 0)⟩
    let prior := Incremental.recertify [] base old.release next.release
    let changed := { base with context := 1 }
    (Engine.choose changed prior.cache old next).incumbent.id = 1 ∧
      (Engine.choose changed prior.cache old next).evaluated = 5 ∧
      Greedy.strictImproves changed old.release next.release = false := by decide

/- The same full greedy query can reuse every positive and negative receipt,
   including both directions of its strict comparisons. -/
theorem integrated_greedy_replay_uses_zero_new_leaf_proofs :
    let old : Engine.Artifact Nat Nat Nat Nat := ⟨1, release (3, 3) (0, 0)⟩
    let first : Engine.Artifact Nat Nat Nat Nat := ⟨2, release (2, 2) (0, 0)⟩
    let second : Engine.Artifact Nat Nat Nat Nat := ⟨3, release (1, 1) (0, 0)⟩
    let cold := Engine.sweep base [] old [first, second]
    let warm := Engine.sweep base cold.cache old [first, second]
    cold.incumbent.id = 3 ∧ cold.evaluated = 7 ∧
      warm.incumbent.id = 3 ∧ warm.evaluated = 0 ∧ warm.reused = 28 := by decide

/- The certified-baseline premise of greedy preservation is necessary.
   A failed starting state does not become certified by refusing candidates. -/
theorem invalid_baseline_is_not_repaired_by_greedy_refusal :
    let old : Engine.Artifact Nat Nat Nat Nat := ⟨1, release (3, 3) (0, 0) []⟩
    let next : Engine.Artifact Nat Nat Nat Nat := ⟨2, release (1, 1) (0, 0)⟩
    let result := Engine.sweep base [] old [next]
    certified base next.release = true ∧ result.incumbent.id = 1 ∧
      certified base result.incumbent.release = false := by decide

/- The checked public entry points close that premise at runtime, including
   the empty-catalogue case in which a raw fold would perform no checks. -/
theorem checked_search_and_deployment_block_invalid_baselines :
    let old : Engine.Artifact Nat Nat Nat Nat := ⟨1, release (3, 3) (0, 0) []⟩
    let next : Engine.Artifact Nat Nat Nat Nat := ⟨2, release (1, 1) (0, 0)⟩
    (Engine.select base [] old []).isNone = true ∧
      (Engine.select base [] old [next]).isNone = true ∧
      (Engine.deploy base [] old next).isNone = true := by decide

/- Maximality over the supplied catalogue is not a theorem that the candidate
   generator has found every feasible release. -/
theorem omitted_candidate_can_dominate_the_catalogue_winner :
    let old := release (3, 3) (0, 0)
    let supplied := release (2, 2) (0, 0)
    let omitted := release (1, 1) (0, 0)
    let winner := Greedy.greedyFrom base old [supplied]
    Greedy.strictImproves base winner supplied = false ∧
      Greedy.strictImproves base winner omitted = true := by decide

end SoftwareDoesntRegress.Dynamic.IndependentControls
