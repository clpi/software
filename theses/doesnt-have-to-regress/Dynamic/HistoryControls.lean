import Dynamic.History
import Audit.ContractControls

set_option autoImplicit false

namespace SoftwareDoesntRegress.Dynamic.HistoryControls

open History
open Audit
open Audit.ContractControls

def initial : State Nat Nat := fun _ => 0

def editTwo : Patch Nat Nat :=
  [{ key := 0, before := 0, after := 7 }, { key := 1, before := 0, after := 9 }]

def edited : State Nat Nat := write (write initial 0 7) 1 9

def forward : Event Nat Nat := { identifier := 10, patch := editTwo }

def genesis : Journal Nat Nat := { current := initial, events := [] }

def committed : Journal Nat Nat := { current := edited, events := [forward] }

/-- A two-key update is executable, and untouched keys retain their values. -/
theorem checked_two_key_update :
    applyPatch initial editTwo = some edited ∧ edited 0 = 7 ∧ edited 1 = 9 ∧ edited 2 = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The inverse restores the entire function, not merely the inspected keys. -/
theorem checked_two_key_inverse_roundtrip :
    applyPatch edited (inverse editTwo) = some initial :=
  apply_inverse_roundtrip checked_two_key_update.1

/-- A stale precondition refuses the entire edit. No partial state is returned. -/
theorem stale_before_value_is_refused :
    applyPatch initial [{ key := 0, before := 1, after := 7 }] = none := by
  rfl

/-- Even a sequentially plausible duplicate-key patch is rejected by the
    public checked operation, so there is no ambiguous same-patch overwrite. -/
theorem duplicate_key_even_sequentially_plausible_is_refused :
    let duplicate : Patch Nat Nat :=
      [{ key := 0, before := 0, after := 1 }, { key := 0, before := 1, after := 2 }]
    run initial duplicate = some (write (write initial 0 1) 0 2) ∧
      applyPatch initial duplicate = none := by
  exact ⟨rfl, rfl⟩

theorem fresh_event_commits : submit genesis forward = some committed := by
  rfl

/-- A replay does not attempt to apply stale before-values again and does
    not append a second event. Exact identifier AND payload match are required. -/
theorem committed_event_replay_is_idempotent :
    submit committed forward = some committed :=
  submission_idempotent fresh_event_commits

theorem reused_identifier_with_different_payload_is_refused :
    submit committed { identifier := 10, patch := [{ key := 0, before := 7, after := 8 }] } = none := by
  rfl

/-- Undo is a new logged operation. The original edit remains in the log. -/
theorem inverse_is_appended_without_erasing_original :
    submit committed (undoEvent 11 forward) =
      some { current := initial, events := [forward, undoEvent 11 forward] } := by
  exact appended_inverse_restores_state_preserves_history [] 11
    checked_two_key_update.1 rfl

/-- A stale inverse may not overwrite a currently mismatching after-value. -/
theorem intervening_edit_blocks_old_inverse :
    applyPatch (write edited 0 8) (inverse editTwo) = none := by
  rfl

theorem undo_cannot_reuse_original_event_identifier :
    submit committed (undoEvent 10 forward) = none := by
  rfl

theorem unrecorded_inverse_source_is_refused : undoRecorded committed 99 11 = none := by
  rfl

/-- Independent challenge: value preconditions do not establish causal
    freshness. An ABA change is invisible after the value returns to 7. -/
theorem aba_value_return_allows_the_old_inverse :
    let afterABA := write (write edited 0 8) 0 7
    applyPatch afterABA (inverse editTwo) = some initial := by
  have h : write (write edited 0 8) 0 7 = edited := by
    funext key
    by_cases hk : key = 0
    · subst key
      rfl
    · simp [write, hk]
  rw [h]
  exact checked_two_key_inverse_roundtrip

/-- The history layer's arbitrary constructor is not an authenticity claim:
    caller-supplied forged state need not equal replay of its claimed log. -/
theorem forged_journal_is_outside_consistency_premise :
    replay initial [forward] = some edited ∧
      edited 0 ≠ initial 0 := by
  exact ⟨rfl, by decide⟩

/-- An old qualification is obsolete after a new cumulative promise. -/
theorem current_promise_refuses_historical_release :
    let current := recordPromises contract (fun _ => [1])
    certified contract baseline = true ∧
      certified current baseline = false ∧
      rollback current feature baseline = some feature := by
  exact ⟨by decide, by decide, rfl⟩

/-- Rollback cannot quietly spend the strict cost improvement just gained. -/
theorem strictly_faster_incumbent_blocks_costly_rollback :
    let faster := release [0] [0] (0, 0)
    replacement contract baseline faster = true ∧
      replacement contract faster baseline = false ∧
      rollback contract faster baseline = some faster := by
  exact ⟨by decide, by decide, rfl⟩

/-- Context is checked against the current contract, not the historic pin. -/
theorem historical_context_certificate_is_not_current_evidence :
    let current := { contract with context := 1 }
    let reobserved := release [0] [0] (1, 1) 1
    certified contract baseline = true ∧
      certified current baseline = false ∧
      rollback current reobserved baseline = some reobserved := by
  exact ⟨by decide, by decide, rfl⟩

/-- Equal-cost rollback is possible if both releases meet all current
    requirements. The extra feature here was never promised. -/
theorem optional_unpromised_feature_can_be_rolled_back :
    rollback contract feature baseline = some baseline := by
  rfl

/-- If a changed contract invalidates the incumbent itself, rollback does
    not silently publish another artifact under a false valid-baseline premise. -/
theorem invalid_current_baseline_blocks_rollback :
    rollback (recordPromises contract (fun _ => [1])) baseline feature = none := by
  rfl

end SoftwareDoesntRegress.Dynamic.HistoryControls
