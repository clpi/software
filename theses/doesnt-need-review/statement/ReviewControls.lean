import Qualification
import Admission
import ExecutableClosure
import ScopedEvidence
import ScopedFrontier
import SoftwareIsQuantifiable.Coverage

namespace ReviewControls

def claimedUnitAgreement (a : Nat) : Prop := a = 0

def noRules (_ : List Nat) (_ : Nat) : Prop := False

def physicalUnitAgreement (_ : Nat) : Prop := (1 : Nat) = 2

theorem derived_claim_can_have_false_interpretation :
    Qualification.Derives claimedUnitAgreement noRules 0 ∧
      ¬ physicalUnitAgreement 0 := by
  exact ⟨Qualification.Derives.root rfl, by
    change ¬ (1 : Nat) = 2
    decide⟩

theorem novel_review_atom_changes_qualification :
    ExecutableClosure.checkedClose [0, 1] [0] [] = some [0] ∧
      ExecutableClosure.checkedClose [0, 1] [0, 1] [] = some [0, 1] ∧
      ExecutableClosure.checkedClose [0, 1] [0] [] ≠
        ExecutableClosure.checkedClose [0, 1] [0, 1] [] := by
  decide

theorem latent_rule_is_conservative_only_at_current_basis :
    ExecutableClosure.checkedClose [0, 1, 2] [0] [] = some [0] ∧
      ExecutableClosure.checkedClose [0, 1, 2] [0] [([1], 2)] = some [0] ∧
      ExecutableClosure.checkedClose [0, 1, 2] [0, 1] [] = some [0, 1] ∧
      ExecutableClosure.checkedClose [0, 1, 2] [0, 1] [([1], 2)] = some [0, 1, 2] := by
  decide

def key : Admission.Key := ⟨0, 0, 0, 0⟩

def payload : Admission.Payload := ⟨0, true, 0⟩

def authorized (_ : Admission.Event) : Bool := true

theorem append_only_history_does_not_make_live_support_monotone :
    Admission.live authorized [.claim key payload] key payload ∧
      Admission.admitted authorized [.claim key payload, .withdraw key]
        (.claim key payload) ∧
      ¬ Admission.live authorized [.claim key payload, .withdraw key] key payload := by
  simp only [Admission.admitted]
  decide

def actualExecution : SoftwareIsQuantifiable.Coverage.Execution := ⟨7⟩

def witnessValid (w : SoftwareIsQuantifiable.Coverage.Witness) : Bool :=
  decide (0 < w.events)

theorem empty_manifest_does_not_cover_an_actual_execution :
    SoftwareIsQuantifiable.Coverage.missing witnessValid [] [] = [] ∧
      SoftwareIsQuantifiable.Coverage.missing witnessValid [] [actualExecution] =
        [actualExecution] ∧
      ¬ Nonempty (SoftwareIsQuantifiable.Coverage.PlatformPremise
        witnessValid [] [actualExecution]) := by
  refine ⟨rfl, rfl, ?_⟩
  apply SoftwareIsQuantifiable.Coverage.empty_ledger_has_no_platform_premise
  simp

def subject : ScopedFrontier.Subject := ⟨0, 0, 0⟩

def alternative : ScopedFrontier.Subject := ⟨1, 0, 0⟩

def contract : ScopedFrontier.Contract where
  scope := 0
  intent := 0
  policy := 0
  preservation := 0
  venue := 0
  harness := 0
  metrics := [⟨0, 0⟩]
  required := [⟨0, 0, 10⟩]
  axes := [⟨0, 0, false⟩]

def input (support : List Nat) (s : ScopedFrontier.Subject) : ScopedFrontier.Input where
  contract := contract
  receipts := [{
    id := 0
    scope := ScopedFrontier.expectedScope contract s 0
    round := 0
    observedPass := support.contains 0
    elapsed := some (if s.artifact = 0 then 2 else 1)
  }]

def reviewKey : Admission.Key := { key with support := 1 }

theorem new_provenance_need_not_change_candidate_admission_or_frontier :
    ¬ Admission.admitted authorized [.claim key payload] (.claim reviewKey payload) ∧
      Admission.admitted authorized [.claim key payload, .claim reviewKey payload]
        (.claim reviewKey payload) ∧
      ScopedFrontier.admitted contract subject (input [0] subject) = true ∧
      ScopedFrontier.admitted contract subject (input [0, 1] subject) = true ∧
      ScopedFrontier.select contract [subject] (input [0]) = [subject] ∧
      ScopedFrontier.select contract [subject] (input [0, 1]) = [subject] := by
  simp only [Admission.admitted]
  decide

def reviewRoots (outcome : Bool) : List Nat :=
  if outcome then [0, 1] else [0]

theorem one_redundant_outcome_does_not_establish_prospective_redundancy :
    ExecutableClosure.checkedClose [0, 1] (reviewRoots false) [] = some [0] ∧
      ¬ (∀ outcome : Bool,
        ExecutableClosure.checkedClose [0, 1] (reviewRoots outcome) [] = some [0]) := by
  decide

theorem raw_duplicate_receipts_can_reverse_qualification :
    ScopedEvidence.qualify ScopedEvidence.examplePolicy
      [ScopedEvidence.receipt0, ScopedEvidence.receipt1] = true ∧
      ScopedEvidence.qualify ScopedEvidence.examplePolicy
        [ScopedEvidence.receipt0, ScopedEvidence.receipt1, ScopedEvidence.receipt0] = false := by
  decide

theorem changing_the_catalogue_changes_the_frontier :
    ScopedFrontier.select contract [subject] (input [0]) = [subject] ∧
      ScopedFrontier.select contract [subject, alternative] (input [0]) = [alternative] := by
  decide

theorem equal_empty_frontiers_do_not_establish_admission :
    ScopedFrontier.select contract [] (input []) = [] ∧
      ScopedFrontier.select contract [subject] (input []) = [] ∧
      ScopedFrontier.admitted contract subject (input [] subject) = false := by
  decide

#print axioms derived_claim_can_have_false_interpretation
#print axioms novel_review_atom_changes_qualification
#print axioms latent_rule_is_conservative_only_at_current_basis
#print axioms append_only_history_does_not_make_live_support_monotone
#print axioms empty_manifest_does_not_cover_an_actual_execution
#print axioms new_provenance_need_not_change_candidate_admission_or_frontier
#print axioms one_redundant_outcome_does_not_establish_prospective_redundancy
#print axioms raw_duplicate_receipts_can_reverse_qualification
#print axioms changing_the_catalogue_changes_the_frontier
#print axioms equal_empty_frontiers_do_not_establish_admission

end ReviewControls
