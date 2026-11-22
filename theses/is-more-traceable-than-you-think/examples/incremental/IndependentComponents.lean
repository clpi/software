import Families

namespace IndependentComponents

def zero : Families.Component := ⟨[⟨.literal 0, [], [.push 0]⟩], 0⟩
def one : Families.Component := ⟨[⟨.literal 1, [], [.push 1]⟩], 0⟩

theorem zero_checked : Families.checked zero = true := by decide
theorem one_checked : Families.checked one = true := by decide

/-- These are the two actual constant blocks used by the factored demo.
    The theorem covers every independent selection, without expansion. -/
theorem every_binary_composition (count : Nat) {selection : List Families.Component}
    (selected : selection ∈ Families.assignments (List.replicate count [zero, one]))
    (env : Pipeline.Environment) :
    ∃ values, Families.sourceTuple env selection = some values ∧
      Families.targetTuple env selection = some values ∧ values.length = count :=
  (Families.binary_component_family_correct zero one zero_checked one_checked count).2.2
    selection selected env

#print axioms zero_checked
#print axioms one_checked
#print axioms every_binary_composition

end IndependentComponents
