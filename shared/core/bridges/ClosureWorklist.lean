-- variant: theses/redundant-compute-expands/proof ClosureWorklist
import SoftwareCore
import ClosureWorklist

namespace SoftwareCore.Bridge.ClosureWorklist

theorem closed_iff (es : List _root_.Canon.ClosureWorklist.Edge) (known : List Nat) :
    _root_.Canon.ClosureWorklist.Closed es known ↔
      SoftwareCore.Closed (SoftwareCore.ofPairs es) (fun x => x ∈ known) := Iff.rfl

end SoftwareCore.Bridge.ClosureWorklist
