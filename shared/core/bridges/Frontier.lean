-- variant: theses/frontier-is-solvable Frontier
import SoftwareCore
import Frontier

namespace SoftwareCore.Bridge.Frontier

theorem noWorse_iff {A I : Type} (cost : A → I → Int) (x y : A) :
    _root_.FrontierSolvable.NoWorse cost x y ↔ SoftwareCore.NoWorse (cost x) (cost y) := Iff.rfl

theorem dominates_iff {A I : Type} (cost : A → I → Int) (x y : A) :
    _root_.FrontierSolvable.Dominates cost x y ↔ SoftwareCore.Dominates (cost x) (cost y) := Iff.rfl

end SoftwareCore.Bridge.Frontier
