import ReviewProofs

namespace ReviewStatement

/-- A decision adapter over the pinned family's checked closure implementation.
    Malformed encoded bases yield `none`; valid unequal relevant closures yield
    `some false`. No universe, relevance, or outcome coverage is inferred. -/
def checkRelevant {A : Type} [DecidableEq A]
    (U₀ U₁ B₀ B₁ : List A) (R₀ R₁ : List (List A × A))
    (relevant : List A) : Option Bool :=
  match ExecutableClosure.checkedClose U₀ B₀ R₀,
      ExecutableClosure.checkedClose U₁ B₁ R₁ with
  | some X, some Y => some (relevant.all (fun a => decide (a ∈ X ↔ a ∈ Y)))
  | _, _ => none

/-- The existing public closure boundary succeeds exactly on its declared
    root/head boundedness condition. Premise lists may contain unreachable atoms. -/
theorem checked_close_success_iff
    {A : Type} [DecidableEq A] (U B : List A) (R : List (List A × A)) :
    (∃ out, ExecutableClosure.checkedClose U B R = some out) ↔
      ExecutableClosure.boundedOK U B R = true := by
  unfold ExecutableClosure.checkedClose
  split
  next bounded =>
    exact ⟨fun _ => bounded, fun _ => ⟨_, rfl⟩⟩
  next unbounded =>
    constructor
    · rintro ⟨_, impossible⟩
      exact False.elim (Option.noConfusion impossible)
    · intro bounded
      exact False.elim (unbounded bounded)

/-- Successful closure results turn the finite comparison into the exact
    relevant qualification proposition, not a heuristic sample comparison. -/
theorem check_relevant_exact_of_outputs
    {A : Type} [DecidableEq A]
    (U₀ U₁ B₀ B₁ : List A) (R₀ R₁ : List (List A × A))
    (relevant X Y : List A)
    (h₀ : ExecutableClosure.checkedClose U₀ B₀ R₀ = some X)
    (h₁ : ExecutableClosure.checkedClose U₁ B₁ R₁ = some Y) :
    checkRelevant U₀ U₁ B₀ B₁ R₀ R₁ relevant = some true ↔
      SameRelevant (fun a => a ∈ relevant)
        (Q (fun a => a ∈ B₀) (fun ps a => (ps, a) ∈ R₀))
        (Q (fun a => a ∈ B₁) (fun ps a => (ps, a) ∈ R₁)) := by
  have exact₀ := (ExecutableClosure.checkedClose_admitted U₀ B₀ R₀ X h₀).2.2
  have exact₁ := (ExecutableClosure.checkedClose_admitted U₁ B₁ R₁ Y h₁).2.2
  simp only [checkRelevant, h₀, h₁, Option.some.injEq, List.all_eq_true,
    decide_eq_true_eq, SameRelevant]
  constructor
  · intro h a ha
    exact (exact₀ a).symm.trans ((h a ha).trans (exact₁ a))
  · intro h a ha
    exact (exact₀ a).trans ((h a ha).trans (exact₁ a).symm)

/-- Exact acceptance: both encoded bases pass their public boundary, and every
    listed relevant atom has equal qualification in the two actual closures. -/
theorem check_relevant_accepts
    {A : Type} [DecidableEq A]
    (U₀ U₁ B₀ B₁ : List A) (R₀ R₁ : List (List A × A)) (relevant : List A) :
    checkRelevant U₀ U₁ B₀ B₁ R₀ R₁ relevant = some true ↔
      ExecutableClosure.boundedOK U₀ B₀ R₀ = true ∧
      ExecutableClosure.boundedOK U₁ B₁ R₁ = true ∧
      SameRelevant (fun a => a ∈ relevant)
        (Q (fun a => a ∈ B₀) (fun ps a => (ps, a) ∈ R₀))
        (Q (fun a => a ∈ B₁) (fun ps a => (ps, a) ∈ R₁)) := by
  constructor
  · intro h
    cases h₀ : ExecutableClosure.checkedClose U₀ B₀ R₀ with
    | none => simp [checkRelevant, h₀] at h
    | some X =>
      cases h₁ : ExecutableClosure.checkedClose U₁ B₁ R₁ with
      | none => simp [checkRelevant, h₀, h₁] at h
      | some Y =>
        exact ⟨(checked_close_success_iff U₀ B₀ R₀).mp ⟨X, h₀⟩,
          (checked_close_success_iff U₁ B₁ R₁).mp ⟨Y, h₁⟩,
          (check_relevant_exact_of_outputs U₀ U₁ B₀ B₁ R₀ R₁ relevant X Y h₀ h₁).mp h⟩
  · rintro ⟨bounded₀, bounded₁, same⟩
    obtain ⟨X, h₀⟩ := (checked_close_success_iff U₀ B₀ R₀).mpr bounded₀
    obtain ⟨Y, h₁⟩ := (checked_close_success_iff U₁ B₁ R₁).mpr bounded₁
    exact (check_relevant_exact_of_outputs U₀ U₁ B₀ B₁ R₀ R₁ relevant X Y h₀ h₁).mpr same

/-- A checked disagreement certifies the existence of an atom in the supplied
    relevant slice whose qualification differs. The Boolean interface does not
    return that witness. Missing inputs remain an independent
    applicability obligation, rather than being silently claimed complete. -/
theorem check_relevant_rejects
    {A : Type} [DecidableEq A]
    (U₀ U₁ B₀ B₁ : List A) (R₀ R₁ : List (List A × A)) (relevant : List A) :
    checkRelevant U₀ U₁ B₀ B₁ R₀ R₁ relevant = some false ↔
      ExecutableClosure.boundedOK U₀ B₀ R₀ = true ∧
      ExecutableClosure.boundedOK U₁ B₁ R₁ = true ∧
      ∃ a, a ∈ relevant ∧
        ¬ (Q (fun x => x ∈ B₀) (fun ps x => (ps, x) ∈ R₀) a ↔
           Q (fun x => x ∈ B₁) (fun ps x => (ps, x) ∈ R₁) a) := by
  have withOutputs : ∀ X Y,
      ExecutableClosure.checkedClose U₀ B₀ R₀ = some X →
      ExecutableClosure.checkedClose U₁ B₁ R₁ = some Y →
      (checkRelevant U₀ U₁ B₀ B₁ R₀ R₁ relevant = some false ↔
        ∃ a, a ∈ relevant ∧
          ¬ (Q (fun x => x ∈ B₀) (fun ps x => (ps, x) ∈ R₀) a ↔
             Q (fun x => x ∈ B₁) (fun ps x => (ps, x) ∈ R₁) a)) := by
    intro X Y h₀ h₁
    have exact₀ := (ExecutableClosure.checkedClose_admitted U₀ B₀ R₀ X h₀).2.2
    have exact₁ := (ExecutableClosure.checkedClose_admitted U₁ B₁ R₁ Y h₁).2.2
    simp only [checkRelevant, h₀, h₁, Option.some.injEq, List.all_eq_false,
      decide_eq_true_eq]
    constructor
    · rintro ⟨a, ha, different⟩
      exact ⟨a, ha, fun same => different
        ((exact₀ a).trans (same.trans (exact₁ a).symm))⟩
    · rintro ⟨a, ha, different⟩
      exact ⟨a, ha, fun same => different
        ((exact₀ a).symm.trans (same.trans (exact₁ a)))⟩
  constructor
  · intro h
    cases h₀ : ExecutableClosure.checkedClose U₀ B₀ R₀ with
    | none => simp [checkRelevant, h₀] at h
    | some X =>
      cases h₁ : ExecutableClosure.checkedClose U₁ B₁ R₁ with
      | none => simp [checkRelevant, h₀, h₁] at h
      | some Y =>
        exact ⟨(checked_close_success_iff U₀ B₀ R₀).mp ⟨X, h₀⟩,
          (checked_close_success_iff U₁ B₁ R₁).mp ⟨Y, h₁⟩,
          (withOutputs X Y h₀ h₁).mp h⟩
  · rintro ⟨bounded₀, bounded₁, different⟩
    obtain ⟨X, h₀⟩ := (checked_close_success_iff U₀ B₀ R₀).mpr bounded₀
    obtain ⟨Y, h₁⟩ := (checked_close_success_iff U₁ B₁ R₁).mpr bounded₁
    exact (withOutputs X Y h₀ h₁).mpr different

/-- Invalid closure inputs are distinguishable from a valid counterexample. -/
theorem check_relevant_unestablished
    {A : Type} [DecidableEq A]
    (U₀ U₁ B₀ B₁ : List A) (R₀ R₁ : List (List A × A)) (relevant : List A) :
    checkRelevant U₀ U₁ B₀ B₁ R₀ R₁ relevant = none ↔
      ExecutableClosure.boundedOK U₀ B₀ R₀ = false ∨
      ExecutableClosure.boundedOK U₁ B₁ R₁ = false := by
  cases h₀ : ExecutableClosure.boundedOK U₀ B₀ R₀ <;>
    cases h₁ : ExecutableClosure.boundedOK U₁ B₁ R₁ <;>
    simp [checkRelevant, ExecutableClosure.checkedClose, h₀, h₁]

/-- Checking a complete finite outcome inventory discharges the uniform
    qualification premise. Completeness of that inventory is an explicit input;
    the checker cannot infer that the real review has no other outcomes. -/
theorem finite_outcomes_conservative
    {A Outcome : Type} [DecidableEq A]
    (U₀ B₀ : List A) (R₀ : List (List A × A))
    (U₁ B₁ : Outcome → List A) (R₁ : Outcome → List (List A × A))
    (relevant : List A) (outcomes : List Outcome) (allowed : Outcome → Prop)
    (outcomes_complete : ∀ o, allowed o → o ∈ outcomes)
    (checked : ∀ o, o ∈ outcomes →
      checkRelevant U₀ (U₁ o) B₀ (B₁ o) R₀ (R₁ o) relevant = some true) :
    ∀ o, allowed o → SameRelevant (fun a => a ∈ relevant)
      (Q (fun a => a ∈ B₀) (fun ps a => (ps, a) ∈ R₀))
      (Q (fun a => a ∈ B₁ o) (fun ps a => (ps, a) ∈ R₁ o)) := by
  intro o ho
  exact ((check_relevant_accepts U₀ (U₁ o) B₀ (B₁ o) R₀ (R₁ o) relevant).mp
    (checked o (outcomes_complete o ho))).2.2

-- Already derivable added root: same qualification on the relevant slice.
#guard checkRelevant [0, 1] [0, 1] [0] [0, 1]
  [([0], 1)] [([0], 1)] [0, 1] == some true
-- Genuinely new relevant root: a checked disagreement, rather than a failure.
#guard checkRelevant [0, 1] [0, 1] [0] [0, 1] [] [] [1] == some false
-- An out-of-universe root is refused even with an empty relevant list.
#guard checkRelevant [0] [0] [0] [1] [] [] [] == none
-- Independent universes and irrelevant added provenance need not be equal.
#guard checkRelevant [0] [0, 1] [0] [0, 1] [] [] [0] == some true

#print axioms checked_close_success_iff
#print axioms check_relevant_exact_of_outputs
#print axioms check_relevant_accepts
#print axioms check_relevant_rejects
#print axioms check_relevant_unestablished
#print axioms finite_outcomes_conservative

end ReviewStatement
