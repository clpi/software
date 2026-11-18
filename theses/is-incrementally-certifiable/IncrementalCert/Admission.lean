import SoftwareIsQuantifiable.Pareto

namespace IncrementalCert

open SoftwareIsQuantifiable.Pareto

def releaseLE {B : Type} [DecidableEq B] (allowed behaviors : List B) : Bool :=
  behaviors.all (fun b => allowed.contains b)

def combinedAdmission {B : Type} [DecidableEq B]
    (allowed : List B) (prior : PriorQualification B) (behaviors : List B) : Bool :=
  !prior.qualified.isEmpty &&
    noQualifiedBehaviorLost prior { offered := behaviors } &&
    releaseLE allowed behaviors

theorem combined_iff {B : Type} [DecidableEq B]
    (allowed : List B) (prior : PriorQualification B) (behaviors : List B) :
    combinedAdmission allowed prior behaviors = true ↔
      prior.qualified ≠ [] ∧
        noQualifiedBehaviorLost prior { offered := behaviors } = true ∧
          releaseLE allowed behaviors = true := by
  cases h : prior.qualified with
  | nil =>
    simp [combinedAdmission, h, List.isEmpty, noQualifiedBehaviorLost, releaseLE]
  | cons b bs =>
    simp [combinedAdmission, h, List.isEmpty, Bool.and_eq_true]

theorem feature_add_fails_releaseLE :
    releaseLE [1] [1, 2] = false ∧
      noQualifiedBehaviorLost ({ qualified := [1] } : PriorQualification Nat)
        ({ offered := [1, 2] } : BehaviorSubmission Nat) = true := by
  decide

theorem removal_fails_acceptsRelease :
    releaseLE [1, 2] [] = true ∧
      noQualifiedBehaviorLost ({ qualified := [1] } : PriorQualification Nat)
        ({ offered := [] } : BehaviorSubmission Nat) = false := by
  decide

theorem empty_required_passes_c4 :
    noQualifiedBehaviorLost ({ qualified := [] } : PriorQualification Nat)
        ({ offered := [] } : BehaviorSubmission Nat) = true ∧
      releaseLE ([] : List Nat) [] = true := by
  decide

end IncrementalCert
