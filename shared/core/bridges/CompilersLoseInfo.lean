-- variant: theses/compilers-lose-info Basic
import SoftwareCore
import Basic

namespace SoftwareCore.Bridge.CompilersLoseInfo

theorem derives_iff {A : Type} (g : _root_.CompilersLoseInfo.Hypergraph A) (a : A) :
    _root_.CompilersLoseInfo.Derives g a ↔ SoftwareCore.Derives g.roots g.edges a := by
  constructor
  · intro d; induction d with
    | root hb => exact .root hb
    | step hr _ ih => exact .step hr ih
  · intro d; induction d with
    | root hb => exact .root hb
    | step hr _ ih => exact .step hr ih

end SoftwareCore.Bridge.CompilersLoseInfo
