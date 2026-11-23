namespace SoftwareDoesntRegress.Audit.Projection

theorem equal_projection_equal_verdict {Execution Observation Verdict : Type}
    (observe : Execution → Observation) (judge : Observation → Verdict)
    {old new : Execution} (h : observe old = observe new) :
    judge (observe old) = judge (observe new) :=
  congrArg judge h

theorem erased_property_has_no_exact_checker {Execution Observation : Type}
    (observe : Execution → Observation) (good : Execution → Prop)
    {old new : Execution} (heq : observe old = observe new)
    (hold : good old) (hnew : ¬ good new) :
    ¬ ∃ judge : Observation → Bool, ∀ r, judge (observe r) = true ↔ good r := by
  rintro ⟨judge, hexact⟩
  have ho := (hexact old).mpr hold
  have hn : judge (observe new) = true := heq ▸ ho
  exact hnew ((hexact new).mp hn)

structure Execution where
  result : Nat
  events : List Nat
  duration : Nat
  environment : Nat

def resultOnly (r : Execution) : Nat := r.result

def old : Execution := ⟨0, [0, 1], 0, 0⟩
def reordered : Execution := ⟨0, [1, 0], 0, 0⟩
def delayed : Execution := ⟨0, [0, 1], 1, 0⟩
def moved : Execution := ⟨0, [0, 1], 0, 1⟩

theorem order_cannot_be_recovered_from_result :
    ¬ ∃ judge : Nat → Bool, ∀ r : Execution,
      judge (resultOnly r) = true ↔ r.events.head? = some 0 := by
  exact erased_property_has_no_exact_checker resultOnly
    (fun r => r.events.head? = some 0) (old := old) (new := reordered)
    rfl (by decide) (by decide)

theorem deadline_cannot_be_recovered_from_result :
    ¬ ∃ judge : Nat → Bool, ∀ r : Execution,
      judge (resultOnly r) = true ↔ r.duration = 0 := by
  exact erased_property_has_no_exact_checker resultOnly
    (fun r => r.duration = 0) (old := old) (new := delayed)
    rfl (by decide) (by decide)

theorem environment_cannot_be_recovered_from_result :
    ¬ ∃ judge : Nat → Bool, ∀ r : Execution,
      judge (resultOnly r) = true ↔ r.environment = 0 := by
  exact erased_property_has_no_exact_checker resultOnly
    (fun r => r.environment = 0) (old := old) (new := moved)
    rfl (by decide) (by decide)

end SoftwareDoesntRegress.Audit.Projection
