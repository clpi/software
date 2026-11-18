import SoftwareIsIncrementallySafe.Checker

namespace SoftwareIsIncrementallySafe.RunAdmission

abbrev Trace := List String

/-- Authenticated scope and policy, independent of the proposed run model. -/
structure Policy where
  inputs : List String
  lowEq : String → String → Bool
  traceAllowed : String → Trace → Bool
  lowView : Trace → Trace
  required : String → List Trace

/-- A finite extracted run model, NOT by itself a certificate of real execution. -/
structure Model where
  runs : String → List Trace

def outputs (p : Policy) (m : Model) (i : String) : List Trace :=
  (m.runs i).map p.lowView

def conditions (p : Policy) (m : Model) : Prop :=
  (∀ i ∈ p.inputs, ∀ t ∈ m.runs i, p.traceAllowed i t = true) ∧
  (∀ i ∈ p.inputs, ∀ t ∈ p.required i, t ∈ m.runs i) ∧
  (∀ i ∈ p.inputs, ∀ j ∈ p.inputs, p.lowEq i j = true →
    (∀ t ∈ outputs p m i, t ∈ outputs p m j) ∧
    (∀ t ∈ outputs p m j, t ∈ outputs p m i))

instance (p : Policy) (m : Model) : Decidable (conditions p m) := by
  unfold conditions
  infer_instance

def check (p : Policy) (m : Model) : Bool := decide (conditions p m)

theorem check_iff (p : Policy) (m : Model) : check p m = true ↔ conditions p m := by
  simp [check]

theorem accepted_ordered_traces (p : Policy) (m : Model) (h : check p m = true) :
    ∀ i ∈ p.inputs, ∀ t ∈ m.runs i, p.traceAllowed i t = true :=
  ((check_iff p m).mp h).1

theorem accepted_relational (p : Policy) (m : Model) (h : check p m = true)
    (i j : String) (hi : i ∈ p.inputs) (hj : j ∈ p.inputs) (he : p.lowEq i j = true) :
    ∀ t, t ∈ outputs p m i ↔ t ∈ outputs p m j := by
  intro t
  have hr := ((check_iff p m).mp h).2.2 i hi j hj he
  exact ⟨hr.1 t, hr.2 t⟩

/-- The external correspondence is an explicit hypothesis, never manufactured
from a hash, an observed sample, or a name. -/
theorem transfer_relational (p : Policy) (m : Model) (h : check p m = true)
    (actual : String → Trace → Prop)
    (correspondence : ∀ i ∈ p.inputs, ∀ t, actual i t ↔ t ∈ outputs p m i)
    (i j : String) (hi : i ∈ p.inputs) (hj : j ∈ p.inputs) (he : p.lowEq i j = true) :
    ∀ t, actual i t ↔ actual j t := by
  intro t
  exact (correspondence i hi t).trans
    ((accepted_relational p m h i j hi hj he t).trans (correspondence j hj t).symm)

def noOpenBeforeStop : Bool → Trace → Bool
  | _, [] => true
  | stopped, e :: es =>
    if e == "stop" then noOpenBeforeStop true es
    else if e == "open" then stopped && noOpenBeforeStop stopped es
    else noOpenBeforeStop stopped es

def trainPolicy : Policy where
  inputs := ["run"]
  lowEq := fun _ _ => true
  traceAllowed := fun _ => noOpenBeforeStop false
  lowView := id
  required := fun _ => []

theorem ordered_allowed : check trainPolicy ⟨fun _ => [["stop", "open"]]⟩ = true := by decide
theorem reversed_refused : check trainPolicy ⟨fun _ => [["open", "stop"]]⟩ = false := by decide

def secretPolicy : Policy where
  inputs := ["0", "1"]
  lowEq := fun _ _ => true
  traceAllowed := fun _ _ => true
  lowView := id
  required := fun _ => []

def leaking : Model := ⟨fun i => [[i]]⟩
def noisy : Model := ⟨fun _ => [["0"], ["1"]]⟩

theorem leaking_refused : check secretPolicy leaking = false := by decide
theorem noisy_accepted : check secretPolicy noisy = true := by decide

def responsePolicy : Policy := { trainPolicy with required := fun _ => [["respond"]] }
theorem empty_response_refused : check responsePolicy ⟨fun _ => []⟩ = false := by decide

end SoftwareIsIncrementallySafe.RunAdmission

#print axioms SoftwareIsIncrementallySafe.RunAdmission.accepted_relational
#print axioms SoftwareIsIncrementallySafe.RunAdmission.transfer_relational
