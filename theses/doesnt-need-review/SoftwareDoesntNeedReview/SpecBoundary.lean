namespace SoftwareDoesntNeedReview

namespace SpecBoundary

inductive Unit where
  | lbfSec
  | newtonSec
deriving DecidableEq, Repr

structure Side where
  role : Nat
  token : Nat
deriving DecidableEq, Repr

def allow (a b : Side) : Bool :=
  a.token == b.token

def denote (role : Nat) : Unit :=
  if role = 0 then Unit.lbfSec else Unit.newtonSec

def ground : Side := ⟨0, 7⟩
def flight : Side := ⟨1, 7⟩

theorem mco_boundary :
    allow ground flight = true ∧
      denote ground.role = Unit.lbfSec ∧
      denote flight.role = Unit.newtonSec ∧
      denote ground.role ≠ denote flight.role := by
  decide

theorem mco_rule_invalid :
    ¬ (allow ground flight = true → denote ground.role = denote flight.role) := by
  intro h
  have hunits : denote ground.role = denote flight.role := h (mco_boundary).1
  exact mco_boundary.2.2.2 hunits

structure Reading where
  sensor : Nat
  aoa : Nat
deriving DecidableEq, Repr

def singleSensor (rs : List Reading) : Bool :=
  rs.any fun r => decide (r.aoa ≤ 10)

def twoSensors (rs : List Reading) : Prop :=
  (rs.filter fun r => decide (r.aoa ≤ 10)).length ≥ 2

def oneSensor : List Reading := [{ sensor := 0, aoa := 5 }]

theorem mcas_boundary :
    singleSensor oneSensor = true ∧ (oneSensor.filter fun r => decide (r.aoa ≤ 10)).length = 1 := by
  decide

theorem mcas_not_two :
    singleSensor oneSensor = true ∧ ¬ twoSensors oneSensor := by
  refine ⟨mcas_boundary.1, ?_⟩
  intro h
  have hlen : (oneSensor.filter fun r => decide (r.aoa ≤ 10)).length = 1 := mcas_boundary.2
  simp [twoSensors, hlen] at h

theorem mcas_rule_invalid :
    ¬ (∀ rs, singleSensor rs = true → twoSensors rs) := by
  intro h
  exact (mcas_not_two).2 (h oneSensor (mcas_not_two).1)

end SpecBoundary

end SoftwareDoesntNeedReview
