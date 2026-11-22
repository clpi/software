import Audit.Contract

set_option autoImplicit false

namespace SoftwareDoesntRegress.Dynamic.History

/-- Pure keyed values only. Reversing a modeled value does not reverse an
    external effect, erase a recorded promise, or authorize deployment. -/
abbrev State (Key Value : Type) := Key → Value

structure Edit (Key Value : Type) where
  key : Key
  before : Value
  after : Value
  deriving DecidableEq, Repr

abbrev Patch (Key Value : Type) := List (Edit Key Value)

def write {Key Value : Type} [DecidableEq Key]
    (state : State Key Value) (key : Key) (value : Value) : State Key Value :=
  fun k => if k = key then value else state k

def reverseEdit {Key Value : Type} (edit : Edit Key Value) : Edit Key Value :=
  { key := edit.key, before := edit.after, after := edit.before }

def inverse {Key Value : Type} (patch : Patch Key Value) : Patch Key Value :=
  (patch.map reverseEdit).reverse

def run {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    (state : State Key Value) : Patch Key Value → Option (State Key Value)
  | [] => some state
  | edit :: rest =>
      if state edit.key = edit.before then
        run (write state edit.key edit.after) rest
      else none

def applyPatch {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    (state : State Key Value) (patch : Patch Key Value) : Option (State Key Value) :=
  if (patch.map Edit.key).Nodup then run state patch else none

theorem write_at {Key Value : Type} [DecidableEq Key]
    (state : State Key Value) (key : Key) (value : Value) :
    write state key value key = value := by
  simp [write]

theorem write_outside {Key Value : Type} [DecidableEq Key]
    (state : State Key Value) (key other : Key) (value : Value)
    (h : other ≠ key) : write state key value other = state other := by
  simp [write, h]

theorem write_restore {Key Value : Type} [DecidableEq Key]
    (state : State Key Value) (edit : Edit Key Value)
    (h : state edit.key = edit.before) :
    write (write state edit.key edit.after) edit.key edit.before = state := by
  funext key
  by_cases hk : key = edit.key
  · subst key
    simp [write, h]
  · simp [write, hk]

theorem reverseEdit_twice {Key Value : Type} (edit : Edit Key Value) :
    reverseEdit (reverseEdit edit) = edit := by
  cases edit
  rfl

theorem inverse_cons {Key Value : Type} (edit : Edit Key Value)
    (rest : Patch Key Value) :
    inverse (edit :: rest) = inverse rest ++ [reverseEdit edit] := by
  simp [inverse]

theorem inverse_twice {Key Value : Type} (patch : Patch Key Value) :
    inverse (inverse patch) = patch := by
  simp [inverse, List.map_reverse, List.map_map, Function.comp_def, reverseEdit_twice]

theorem run_append {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    (state : State Key Value) (first second : Patch Key Value) :
    run state (first ++ second) = (run state first).bind (fun next => run next second) := by
  induction first generalizing state with
  | nil => rfl
  | cons edit rest ih =>
      by_cases h : state edit.key = edit.before
      · simp [run, h, ih]
      · simp [run, h]

theorem run_inverse {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    {state next : State Key Value} {patch : Patch Key Value}
    (h : run state patch = some next) :
    run next (inverse patch) = some state := by
  induction patch generalizing state next with
  | nil =>
      simp only [run, Option.some.injEq] at h
      subst next
      rfl
  | cons edit rest ih =>
      by_cases hbefore : state edit.key = edit.before
      · have htail : run (write state edit.key edit.after) rest = some next := by
          simpa only [run, if_pos hbefore] using h
        rw [inverse_cons, run_append, ih htail]
        change (if write state edit.key edit.after edit.key = edit.after then
          some (write (write state edit.key edit.after) edit.key edit.before)
          else none) = some state
        rw [if_pos (write_at state edit.key edit.after), write_restore state edit hbefore]
      · simp [run, hbefore] at h

theorem inverse_preserves_unique_keys {Key Value : Type}
    {patch : Patch Key Value} (h : (patch.map Edit.key).Nodup) :
    ((inverse patch).map Edit.key).Nodup := by
  simpa [inverse, List.map_reverse, List.map_map, reverseEdit, Function.comp_def] using
    h.perm (List.reverse_perm _).symm

theorem applied_has_unique_keys {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {state next : State Key Value} {patch : Patch Key Value}
    (h : applyPatch state patch = some next) : (patch.map Edit.key).Nodup := by
  unfold applyPatch at h
  split at h
  · assumption
  · contradiction

theorem applied_runs {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    {state next : State Key Value} {patch : Patch Key Value}
    (h : applyPatch state patch = some next) : run state patch = some next := by
  unfold applyPatch at h
  split at h
  · exact h
  · contradiction

theorem apply_inverse_roundtrip {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {state next : State Key Value} {patch : Patch Key Value}
    (h : applyPatch state patch = some next) :
    applyPatch next (inverse patch) = some state := by
  rw [applyPatch, if_pos (inverse_preserves_unique_keys (applied_has_unique_keys h))]
  exact run_inverse (applied_runs h)

theorem duplicate_keys_refused {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    (state : State Key Value) {patch : Patch Key Value}
    (h : ¬ (patch.map Edit.key).Nodup) : applyPatch state patch = none := by
  simp [applyPatch, h]

theorem run_preserves_unedited_key {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {state next : State Key Value} {patch : Patch Key Value} {key : Key}
    (h : run state patch = some next) (houtside : key ∉ patch.map Edit.key) :
    next key = state key := by
  induction patch generalizing state next with
  | nil =>
      simp only [run, Option.some.injEq] at h
      subst next
      rfl
  | cons edit rest ih =>
      have hne : key ≠ edit.key := by
        intro heq
        apply houtside
        simp [heq]
      have hrest : key ∉ rest.map Edit.key := by
        intro hm
        exact houtside (by simp [hm])
      by_cases hbefore : state edit.key = edit.before
      · have htail : run (write state edit.key edit.after) rest = some next := by
          simpa only [run, if_pos hbefore] using h
        exact (ih htail hrest).trans (write_outside state edit.key key edit.after hne)
      · simp [run, hbefore] at h

theorem applied_patch_preserves_unedited_key {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {state next : State Key Value} {patch : Patch Key Value} {key : Key}
    (h : applyPatch state patch = some next) (houtside : key ∉ patch.map Edit.key) :
    next key = state key :=
  run_preserves_unedited_key (applied_runs h) houtside

structure Event (Key Value : Type) where
  identifier : Nat
  patch : Patch Key Value
  deriving DecidableEq, Repr

structure Journal (Key Value : Type) where
  current : State Key Value
  events : List (Event Key Value)

def lookup {Key Value : Type} (identifier : Nat) :
    List (Event Key Value) → Option (Event Key Value)
  | [] => none
  | event :: rest => if event.identifier = identifier then some event else lookup identifier rest

/-- The caller supplies a consistent genesis journal. The preservation
    theorems below retain replay consistency and identifier uniqueness;
    this operation does not certify a forged input journal. -/
def submit {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    (journal : Journal Key Value) (event : Event Key Value) : Option (Journal Key Value) :=
  match lookup event.identifier journal.events with
  | some prior => if prior = event then some journal else none
  | none =>
      match applyPatch journal.current event.patch with
      | none => none
      | some next => some { current := next, events := journal.events ++ [event] }

theorem lookup_append_of_absent {Key Value : Type} (identifier : Nat)
    (first second : List (Event Key Value)) (h : lookup identifier first = none) :
    lookup identifier (first ++ second) = lookup identifier second := by
  induction first with
  | nil => rfl
  | cons event rest ih =>
      by_cases hi : event.identifier = identifier
      · simp [lookup, hi] at h
      · simpa [lookup, hi] using ih (by simpa [lookup, hi] using h)

theorem lookup_none_iff {Key Value : Type} (identifier : Nat)
    (events : List (Event Key Value)) :
    lookup identifier events = none ↔ ∀ e ∈ events, e.identifier ≠ identifier := by
  induction events with
  | nil => simp [lookup]
  | cons e rest ih =>
      by_cases he : e.identifier = identifier
      · simp [lookup, he]
      · simp [lookup, he, ih]

theorem replay_same_key_payload {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {journal : Journal Key Value} {event : Event Key Value}
    (h : lookup event.identifier journal.events = some event) :
    submit journal event = some journal := by
  simp [submit, h]

theorem conflicting_key_payload_refused {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {journal : Journal Key Value} {event prior : Event Key Value}
    (h : lookup event.identifier journal.events = some prior)
    (hne : prior ≠ event) : submit journal event = none := by
  simp [submit, h, hne]

theorem successful_submission_shape {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {journal result : Journal Key Value} {event : Event Key Value}
    (h : submit journal event = some result) :
    result = journal ∨
      (result.events = journal.events ++ [event] ∧
        applyPatch journal.current event.patch = some result.current ∧
        lookup event.identifier journal.events = none) := by
  cases hlookup : lookup event.identifier journal.events with
  | some prior =>
      simp only [submit, hlookup] at h
      by_cases heq : prior = event
      · simp only [if_pos heq, Option.some.injEq] at h
        exact Or.inl h.symm
      · simp [heq] at h
  | none =>
      simp only [submit, hlookup] at h
      cases hpatch : applyPatch journal.current event.patch with
      | none => simp [hpatch] at h
      | some next =>
          simp only [hpatch, Option.some.injEq] at h
          subst result
          exact Or.inr ⟨rfl, rfl, rfl⟩

theorem submission_keeps_history_prefix {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {journal result : Journal Key Value} {event : Event Key Value}
    (h : submit journal event = some result) :
    ∃ suffix, result.events = journal.events ++ suffix := by
  rcases successful_submission_shape h with hsame | ⟨happend, _, _⟩
  · exact ⟨[], by simp [hsame]⟩
  · exact ⟨[event], happend⟩

theorem submission_idempotent {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {journal result : Journal Key Value} {event : Event Key Value}
    (h : submit journal event = some result) :
    submit result event = some result := by
  rcases successful_submission_shape h with hsame | ⟨happend, _, habsent⟩
  · subst result
    exact h
  · apply replay_same_key_payload
    rw [happend, lookup_append_of_absent event.identifier _ _ habsent]
    simp [lookup]

theorem submission_preserves_unique_identifiers {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {journal result : Journal Key Value} {event : Event Key Value}
    (hunique : (journal.events.map Event.identifier).Nodup)
    (h : submit journal event = some result) :
    (result.events.map Event.identifier).Nodup := by
  rcases successful_submission_shape h with hsame | ⟨happend, _, habsent⟩
  · simpa [hsame] using hunique
  · rw [happend, List.map_append]
    have hnot : event.identifier ∉ journal.events.map Event.identifier := by
      intro hm
      obtain ⟨e, he, hi⟩ := List.mem_map.mp hm
      exact ((lookup_none_iff event.identifier journal.events).mp habsent e he) hi
    change (journal.events.map Event.identifier ++ [event.identifier]).Pairwise (· ≠ ·)
    apply List.pairwise_append.mpr
    refine ⟨hunique, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    intro heq
    apply hnot
    simpa [heq] using hx

def replay {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    (initial : State Key Value) (events : List (Event Key Value)) : Option (State Key Value) :=
  run initial (events.flatMap Event.patch)

theorem submission_preserves_replay {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    (initial : State Key Value)
    {journal result : Journal Key Value} {event : Event Key Value}
    (hconsistent : replay initial journal.events = some journal.current)
    (h : submit journal event = some result) :
    replay initial result.events = some result.current := by
  rcases successful_submission_shape h with hsame | ⟨happend, hpatch, _⟩
  · simpa [hsame] using hconsistent
  · simp only [replay] at hconsistent ⊢
    rw [happend, List.flatMap_append, run_append, hconsistent]
    simpa using applied_runs hpatch

def undoEvent {Key Value : Type} (identifier : Nat) (event : Event Key Value) : Event Key Value :=
  { identifier := identifier, patch := inverse event.patch }

/-- A checked historical undo requires a recorded source event. Its guard
    compares current values, not hidden causal revisions: an ABA return to
    the same after-value can satisfy it. External effects remain out of model. -/
def undoRecorded {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    (journal : Journal Key Value) (priorIdentifier identifier : Nat) :
    Option (Journal Key Value) :=
  match lookup priorIdentifier journal.events with
  | none => none
  | some prior => submit journal (undoEvent identifier prior)

theorem undo_unknown_event_refused {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    (journal : Journal Key Value) (priorIdentifier identifier : Nat)
    (h : lookup priorIdentifier journal.events = none) :
    undoRecorded journal priorIdentifier identifier = none := by
  simp [undoRecorded, h]

theorem undo_recorded_event_uses_exact_inverse {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    (journal : Journal Key Value) (priorIdentifier identifier : Nat)
    (prior : Event Key Value) (h : lookup priorIdentifier journal.events = some prior) :
    undoRecorded journal priorIdentifier identifier = submit journal (undoEvent identifier prior) := by
  simp [undoRecorded, h]

theorem appended_inverse_restores_state_preserves_history {Key Value : Type}
    [DecidableEq Key] [DecidableEq Value]
    {before after : State Key Value} {event : Event Key Value}
    (events : List (Event Key Value)) (identifier : Nat)
    (hpatch : applyPatch before event.patch = some after)
    (hfresh : lookup identifier (events ++ [event]) = none) :
    submit { current := after, events := events ++ [event] } (undoEvent identifier event) =
      some { current := before, events := (events ++ [event]) ++ [undoEvent identifier event] } := by
  simp only [submit, undoEvent, hfresh]
  rw [apply_inverse_roundtrip hpatch]

/-- A historical release is a candidate under the current contract and
    incumbent costs. The contract and append-only evidence are not undone. -/
def rollback {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (contract : Audit.Contract Capability Outcome Key Context)
    (current historical : Audit.ScopedRelease Capability Outcome Key Context) :=
  Audit.deploy contract current historical

theorem rollback_recertifies_current_contract {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {contract : Audit.Contract Capability Outcome Key Context}
    {current historical result : Audit.ScopedRelease Capability Outcome Key Context}
    (h : rollback contract current historical = some result) :
    Audit.replacement contract current result = true :=
  Audit.deployed_safe h

theorem strict_improvement_cannot_be_reversed_without_cost_regression
    {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {contract : Audit.Contract Capability Outcome Key Context}
    {current historical : Audit.ScopedRelease Capability Outcome Key Context}
    {key : Key} (hk : key ∈ contract.keys)
    (hbetter : SoftwareIsQuantifiable.Pareto.dominates
      (current.profile key).cost (historical.profile key).cost) :
    Audit.replacement contract current historical = false := by
  cases h : Audit.replacement contract current historical with
  | false => rfl
  | true => exact False.elim ((Audit.no_strict_reverse_dominance h hk) hbetter)

theorem reversible_nonregression_has_equal_represented_costs
    {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {contract : Audit.Contract Capability Outcome Key Context}
    {a b : Audit.ScopedRelease Capability Outcome Key Context}
    (hab : Audit.replacement contract a b = true)
    (hba : Audit.replacement contract b a = true)
    {key : Key} (hk : key ∈ contract.keys) :
    (a.profile key).cost = (b.profile key).cost := by
  have hab := ((Audit.replacement_iff contract a b).mp hab).2.2 key hk
  have hba := ((Audit.replacement_iff contract b a).mp hba).2.2 key hk
  exact Prod.ext (Nat.le_antisymm hba.1 hab.1) (Nat.le_antisymm hba.2 hab.2)

end SoftwareDoesntRegress.Dynamic.History
