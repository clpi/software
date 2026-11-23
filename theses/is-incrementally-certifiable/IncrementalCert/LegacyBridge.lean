import IncrementalCert.LegacySequence
import SoftwareIsQuantifiable.Pareto

set_option autoImplicit false

namespace IncrementalCert.LegacyBridge

open Legacy.SoftwareIsIncrementallyCertifiable
open SoftwareIsQuantifiable

def point (cost : Cost) : Pareto.Point := (cost.time, cost.compute)

theorem weak_iff_canonical (a b : Cost) :
    paretoLE a b ↔ Interface.noWorse Pareto.costSpace
      (Pareto.profileOf (point a)) (Pareto.profileOf (point b)) := by
  simp [paretoLE, Interface.noWorse, Interface.measuresLe, Interface.behaviorLe,
    Pareto.profileOf, point, Pareto.costSpace, Interface.axesLe, Interface.axisLe]

theorem strict_iff_canonical (a b : Cost) :
    paretoDominates a b ↔ Interface.dominates Pareto.costSpace
      (Pareto.profileOf (point a)) (Pareto.profileOf (point b)) := by
  rw [← Pareto.dominates_iff_interface]
  simp [paretoDominates, paretoLE, Pareto.dominates, point, and_assoc]

theorem canonical_cost_sequence (costs : Nat → Cost)
    (h : ∀ n, paretoLE (costs (n + 1)) (costs n))
    {i j : Nat} (hij : i ≤ j) :
    Interface.noWorse Pareto.costSpace
      (Pareto.profileOf (point (costs j))) (Pareto.profileOf (point (costs i))) :=
  (weak_iff_canonical (costs j) (costs i)).mp
    (LegacySequence.cost_global_of_adjacent costs h hij)

end IncrementalCert.LegacyBridge
