-- variant: theses/persistence-is-minimal/proof Core
import SoftwareCore
import Core

namespace SoftwareCore.Bridge.Persistence

/-- The named axes are the index set of the canonical cost vector. -/
theorem dominates_iff (axes : List (Nat → Nat → Nat)) (d s r : List Nat) :
    _root_.Persistence.Dominates axes d s r ↔
      SoftwareCore.Dominates (I := {a // a ∈ axes})
        (fun a => _root_.Persistence.cost a.1 d s) (fun a => _root_.Persistence.cost a.1 d r) := by
  constructor
  · intro ⟨h1, a, ha, h2⟩
    exact ⟨fun ⟨b, hb⟩ => h1 b hb, ⟨a, ha⟩, h2⟩
  · intro ⟨h1, ⟨a, ha⟩, h2⟩
    exact ⟨fun b hb => h1 ⟨b, hb⟩, a, ha, h2⟩

end SoftwareCore.Bridge.Persistence
