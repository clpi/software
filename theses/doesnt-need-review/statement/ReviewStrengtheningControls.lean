import ReviewOmission
import ReviewFinite
import ReviewControls

namespace ReviewStrengtheningControls

open ReviewStatement
open ReviewControls (subject alternative contract)

def latentRule (ps : List Nat) (a : Nat) : Prop := ps = [1] ∧ a = 2

theorem one_sided_inclusion_does_not_imply_target_rule_closure :
    (∀ a, Q (fun _ : Nat => False) latentRule a →
      Q (fun a : Nat => a = 1) (fun _ _ => False) a) ∧
    ¬ Qualification.Closed latentRule
      (Q (fun a : Nat => a = 1) (fun _ _ => False)) := by
  constructor
  · intro a h
    have impossible : ∀ a, Q (fun _ : Nat => False) latentRule a → False :=
      Qualification.least (fun _ h => h) (by
        intro ps a hr hp
        obtain ⟨rfl, rfl⟩ := hr
        exact hp 1 (by simp))
    exact False.elim (impossible a h)
  · intro closed
    have derivesTwo : Q (fun a : Nat => a = 1) (fun _ _ => False) 2 :=
      closed [1] 2 ⟨rfl, rfl⟩ (by
        intro p hp
        have one : p = 1 := by simpa using hp
        exact Qualification.Derives.root one)
    have onlyOne : ∀ a,
        Q (fun a : Nat => a = 1) (fun _ _ => False) a → a = 1 :=
      Qualification.least (fun _ h => h) (by
        intro _ _ h _
        exact False.elim h)
    have impossible := onlyOne 2 derivesTwo
    contradiction

def pricedInput (receiptId : Nat) (value : ScopedFrontier.Subject → Nat)
    (passed : ScopedFrontier.Subject → Bool) (s : ScopedFrontier.Subject) :
    ScopedFrontier.Input where
  contract := contract
  receipts := [{
    id := receiptId
    scope := ScopedFrontier.expectedScope contract s 0
    round := 0
    observedPass := passed s
    elapsed := some (value s)
  }]

def before : ScopedFrontier.Subject → ScopedFrontier.Input :=
  pricedInput 0 (fun s => if s.artifact = 0 then 2 else 1) (fun _ => true)

def reversed : ScopedFrontier.Subject → ScopedFrontier.Input :=
  pricedInput 0 (fun s => if s.artifact = 0 then 1 else 2) (fun _ => true)

theorem equal_admission_does_not_preserve_frontier :
    (∀ s,
      ScopedFrontier.admitted contract s (before s) =
        ScopedFrontier.admitted contract s (reversed s)) ∧
    ScopedFrontier.select contract [subject, alternative] before = [alternative] ∧
    ScopedFrontier.select contract [subject, alternative] reversed = [subject] := by
  constructor
  · intro s
    by_cases h : s.artifact = 0 <;>
      simp [before, reversed, pricedInput, ScopedFrontier.admitted,
        ScopedFrontier.aligned, ScopedEvidence.qualify, ScopedFrontier.expectedPolicy,
        ScopedEvidence.checkRequirement, ScopedFrontier.coordinate,
        ScopedFrontier.requirementMatches, ScopedEvidence.matchingKey,
        ScopedFrontier.expectedScope, contract, h, EligibleSchedules.timingOK]
  · decide

def refusedDominated : ScopedFrontier.Subject → ScopedFrontier.Input :=
  pricedInput 0 (fun s => if s.artifact = 0 then 2 else 1)
    (fun s => s.artifact != 0)

theorem equal_frontier_does_not_preserve_all_admissions :
    ScopedFrontier.select contract [subject, alternative] before = [alternative] ∧
    ScopedFrontier.select contract [subject, alternative] refusedDominated = [alternative] ∧
    ScopedFrontier.admitted contract subject (before subject) = true ∧
    ScopedFrontier.admitted contract subject (refusedDominated subject) = false := by
  decide

def distinctProvenance : ScopedFrontier.Subject → ScopedFrontier.Input :=
  pricedInput 1 (fun s => if s.artifact = 0 then 2 else 1) (fun _ => true)

private theorem provenance_admissions_equal (s : ScopedFrontier.Subject) :
    ScopedFrontier.admitted contract s (before s) =
      ScopedFrontier.admitted contract s (distinctProvenance s) := by
  simp [before, distinctProvenance, pricedInput, ScopedFrontier.admitted,
    ScopedFrontier.aligned, ScopedEvidence.qualify, ScopedFrontier.expectedPolicy,
    ScopedEvidence.checkRequirement, ScopedFrontier.coordinate,
    ScopedFrontier.requirementMatches, ScopedEvidence.matchingKey,
    ScopedFrontier.expectedScope, contract]

theorem equal_observations_do_not_require_equal_input :
    before subject ≠ distinctProvenance subject ∧
    (∀ s,
      ScopedFrontier.admitted contract s (before s) =
        ScopedFrontier.admitted contract s (distinctProvenance s)) ∧
    ScopedFrontier.select contract [subject, alternative] before = [alternative] ∧
    ScopedFrontier.select contract [subject, alternative] distinctProvenance = [alternative] := by
  exact ⟨by decide, provenance_admissions_equal, by decide, by decide⟩

theorem decisions_do_not_determine_relevant_qualification :
    SameDecisions contract [subject, alternative]
      (fun (_ : Nat → Prop) => before)
      (fun a => a = 0) (fun a => a = 0 ∨ a = 1) ∧
    ¬ SameRelevant (fun a => a = 1)
      (fun a => a = 0) (fun a => a = 0 ∨ a = 1) := by
  constructor
  · exact ⟨fun _ => rfl, rfl⟩
  · intro same
    have impossible : (1 : Nat) = 0 :=
      (same 1 rfl).mpr (Or.inr rfl)
    contradiction

noncomputable def provenanceProject (X : Nat → Prop) :
    ScopedFrontier.Subject → ScopedFrontier.Input := by
  classical
  exact if X 0 then distinctProvenance else before

theorem decision_noninterference_strictly_weaker_than_input_noninterference :
    RespectsDecisions (fun a : Nat => a = 1) provenanceProject contract
      [subject, alternative] ∧
    ¬ RespectsRelevant (fun a : Nat => a = 1) provenanceProject ∧
    ScopedFrontier.admitted contract subject
      (provenanceProject (fun a => a = 1) subject) = true := by
  constructor
  · intro X Y _
    by_cases hx : X 0 <;> by_cases hy : Y 0
    · simp [SameDecisions, provenanceProject, hx, hy]
    · simp only [SameDecisions, provenanceProject, hx, hy, ↓reduceIte]
      exact ⟨fun s => (provenance_admissions_equal s).symm, by decide⟩
    · simp only [SameDecisions, provenanceProject, hx, hy, ↓reduceIte]
      exact ⟨provenance_admissions_equal, by decide⟩
    · simp [SameDecisions, provenanceProject, hx, hy]
  · constructor
    · intro respects
      have same : SameRelevant (fun a : Nat => a = 1)
          (fun a => a = 1) (fun a => a = 1 ∨ a = 0) := by
        intro a ha
        exact ⟨fun h => Or.inl h, fun _ => ha⟩
      have equal := congrArg (fun f => f subject)
        (respects (fun a => a = 1) (fun a => a = 1 ∨ a = 0) same)
      have impossible : before subject = distinctProvenance subject := by
        simpa only [provenanceProject, Nat.zero_ne_one, or_true, ↓reduceIte] using equal
      exact equal_observations_do_not_require_equal_input.1 impossible
    · simp only [provenanceProject, Nat.zero_ne_one, ↓reduceIte]
      decide

theorem incomplete_outcome_inventory_can_hide_a_checked_difference :
    (∀ o ∈ [false], checkRelevant [0, 1] [0, 1] [0]
      (ReviewControls.reviewRoots o) [] [] [1] = some true) ∧
    checkRelevant [0, 1] [0, 1] [0]
      (ReviewControls.reviewRoots true) [] [] [1] = some false ∧
    ¬ (∀ o : Bool, o ∈ [false]) := by
  decide

theorem omitted_relevant_atoms_can_hide_a_checked_difference :
    checkRelevant [0, 1] [0, 1] [0] [0, 1] [] [] [] = some true ∧
    checkRelevant [0, 1] [0, 1] [0] [0, 1] [] [] [2] = some true ∧
    checkRelevant [0, 1] [0, 1] [0] [0, 1] [] [] [1] = some false := by
  decide

#print axioms one_sided_inclusion_does_not_imply_target_rule_closure
#print axioms equal_admission_does_not_preserve_frontier
#print axioms equal_frontier_does_not_preserve_all_admissions
#print axioms equal_observations_do_not_require_equal_input
#print axioms decisions_do_not_determine_relevant_qualification

#print axioms decision_noninterference_strictly_weaker_than_input_noninterference

#print axioms incomplete_outcome_inventory_can_hide_a_checked_difference
#print axioms omitted_relevant_atoms_can_hide_a_checked_difference

end ReviewStrengtheningControls
