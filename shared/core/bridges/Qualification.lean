-- variant: theses/optimality Qualification
-- Also covers the byte-identical copies in theses/testing-is-redundant and
-- theses/benchmarking-is-redundant-and-suboptimal (consolidation/check-copies.py).
import SoftwareCore
import Qualification

namespace SoftwareCore.Bridge.Qualification
universe u
variable {A : Type u}

theorem derives_iff (B : A → Prop) (R : List A → A → Prop) (a : A) :
    _root_.Qualification.Derives B R a ↔ SoftwareCore.Derives B R a := by
  constructor
  · intro d; induction d with
    | root hb => exact .root hb
    | step hr _ ih => exact .step hr ih
  · intro d; induction d with
    | root hb => exact .root hb
    | step hr _ ih => exact .step hr ih

theorem closed_iff (R : List A → A → Prop) (X : A → Prop) :
    _root_.Qualification.Closed R X ↔ SoftwareCore.Closed R X := Iff.rfl

end SoftwareCore.Bridge.Qualification
