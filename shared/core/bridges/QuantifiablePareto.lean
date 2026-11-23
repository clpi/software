-- variant: theses/is-quantifiable SoftwareIsQuantifiable.Pareto
import SoftwareCore
import SoftwareIsQuantifiable.Pareto

namespace SoftwareCore.Bridge.QuantifiablePareto
open _root_.SoftwareIsQuantifiable.Pareto (Point)

theorem noWorse_iff (a b : Point) :
    _root_.SoftwareIsQuantifiable.Pareto.noWorse a b ↔
      SoftwareCore.NoWorse (SoftwareCore.pairVec a) (SoftwareCore.pairVec b) :=
  (SoftwareCore.noWorse_pair a b).symm

theorem dominates_iff (a b : Point) :
    _root_.SoftwareIsQuantifiable.Pareto.dominates a b ↔
      SoftwareCore.Dominates (SoftwareCore.pairVec a) (SoftwareCore.pairVec b) := by
  unfold _root_.SoftwareIsQuantifiable.Pareto.dominates SoftwareCore.Dominates
  rw [SoftwareCore.noWorse_pair]
  constructor
  · intro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    cases h3 with
    | inl h => exact ⟨true, h⟩
    | inr h => exact ⟨false, h⟩
  · intro ⟨⟨h1, h2⟩, b, h⟩
    refine ⟨h1, h2, ?_⟩
    cases b
    · exact Or.inr h
    · exact Or.inl h

end SoftwareCore.Bridge.QuantifiablePareto
