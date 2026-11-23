-- variant: theses/is-incrementally-safe Family.Saturation
import SoftwareCore
import Family.Saturation

namespace SoftwareCore.Bridge.Saturation

theorem derives_iff {F : Type} (base : F → Prop) (rules : List (List F × F)) (x : F) :
    _root_.Family.Saturation.Derives base rules x ↔
      SoftwareCore.Derives base (SoftwareCore.ofPairs rules) x := by
  constructor
  · intro d; induction d with
    | base hb => exact .root hb
    | rule hr _ ih => exact .step (show (_, _) ∈ rules from hr) ih
  · intro d; induction d with
    | root hb => exact .base hb
    | @step ps a hr _ ih => exact _root_.Family.Saturation.Derives.rule (r := (ps, a)) hr ih

end SoftwareCore.Bridge.Saturation
