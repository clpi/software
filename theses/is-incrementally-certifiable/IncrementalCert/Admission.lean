import SoftwareIsComposable

namespace IncrementalCert

def releaseLE (allowed behaviors : List Nat) : Bool :=
  behaviors.all (fun b => allowed.contains b)

def acceptsRelease (required behaviors : List Nat) : Bool :=
  SoftwareIsComposable.accepts required behaviors

def combinedAdmission (allowed required behaviors : List Nat) : Bool :=
  releaseLE allowed behaviors && acceptsRelease required behaviors

theorem combined_iff (allowed required behaviors : List Nat) :
    combinedAdmission allowed required behaviors = true ↔
      releaseLE allowed behaviors = true ∧
        acceptsRelease required behaviors = true := by
  simp [combinedAdmission, Bool.and_eq_true]

theorem feature_add_fails_releaseLE :
    releaseLE [1] [1, 2] = false ∧ acceptsRelease [1] [1, 2] = true := by
  decide

theorem removal_fails_acceptsRelease :
    releaseLE [1, 2] [] = true ∧ acceptsRelease [1] [] = false := by
  decide

theorem empty_required_passes_c4 :
    (([] : List Nat).all (fun b => ([] : List Nat).contains b)) = true ∧
      acceptsRelease [] [] = true := by
  decide

end IncrementalCert
