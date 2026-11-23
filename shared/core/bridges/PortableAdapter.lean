-- variant: theses/optimality/portable-evidence/lean PortableAdapter
import SoftwareCore
import PortableAdapter

namespace SoftwareCore.Bridge.PortableAdapter
open _root_.PortableAdapter (Edge)

theorem derives_iff (roots : String → Prop) (edges : List Edge) (x : String) :
    _root_.PortableAdapter.Derives roots edges x ↔
      SoftwareCore.Derives roots (SoftwareCore.ofRecords Edge.premises Edge.conclusion edges) x := by
  constructor
  · intro d; induction d with
    | root hr => exact .root hr
    | @step e he _ ih => exact .step ⟨e, he, rfl, rfl⟩ ih
  · intro d; induction d with
    | root hr => exact .root hr
    | step hr _ ih =>
      obtain ⟨e, he, hp, hc⟩ := hr
      subst hp; subst hc
      exact .step he ih

end SoftwareCore.Bridge.PortableAdapter
