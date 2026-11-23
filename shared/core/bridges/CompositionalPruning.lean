-- variant: theses/is-reversible/examples/resolution-lab/proof CompositionalPruning
import SoftwareCore
import CompositionalPruning

namespace SoftwareCore.Bridge.CompositionalPruning
universe u

theorem weak_iff {Axis : Type u} (x y : _root_.CompositionalPruning.Cost Axis) :
    _root_.CompositionalPruning.Weak x y ↔ SoftwareCore.NoWorse x y := Iff.rfl

theorem dominates_iff {Axis : Type u} (x y : _root_.CompositionalPruning.Cost Axis) :
    _root_.CompositionalPruning.Dominates x y ↔ SoftwareCore.Dominates x y := Iff.rfl

end SoftwareCore.Bridge.CompositionalPruning
