import SoftwareIsComposable.Interaction
import SoftwareIsComposable.InteractionModel

namespace SoftwareIsComposable.OneShotBoundary

open InteractionModel

def noSeeds : Component → List Observation := fun _ => []

def nullaryRule : Rule := ⟨[], 42⟩

theorem nullary_effect_without_components :
    observations noSeeds [] [nullaryRule] = [42] := rfl

theorem empty_selection_need_not_be_safe :
    ¬ inSpec (fun _ => false) noSeeds [] [nullaryRule] := by
  unfold inSpec
  rw [nullary_effect_without_components]
  decide

def chainSeeds : Component → List Observation := fun _ => [0]

def chainRules : List Rule := [⟨[(0, 0)], 1⟩, ⟨[(0, 1)], 2⟩]

theorem finite_chain_outputs :
    observations chainSeeds [0] chainRules = [0, 1] := by decide

theorem finite_effects_do_not_feed_back :
    2 ∉ observations chainSeeds [0] chainRules := by
  rw [finite_chain_outputs]
  decide

def recursiveEmpty : Unit → Legacy.Profile Nat := fun _ => ⟨fun _ => False⟩

def noDeps (_s _t : Unit) : Prop := False

theorem recursive_empty_seeds_cannot_emit
    (deps : Unit → Unit → Prop) (join : Interaction.Join Nat) (o : Nat) {s : Unit} :
    ¬ Interaction.Reaches deps join recursiveEmpty s o := by
  intro h
  induction h with
  | here hobs => exact hobs
  | step _ _ ih => exact ih
  | interact _ _ _ ih _ => exact ih

def recursiveSeeds : Unit → Legacy.Profile Nat := fun _ => ⟨fun o => o = 0⟩

def recursiveRules : Interaction.Join Nat := fun a b c =>
  (a = 0 ∧ b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1 ∧ c = 2)

theorem recursive_first_effect :
    Interaction.Reaches noDeps recursiveRules recursiveSeeds () 1 :=
  .interact (Or.inl ⟨rfl, rfl, rfl⟩) (.here rfl) (.here rfl)

theorem recursive_effects_do_feed_back :
    Interaction.Reaches noDeps recursiveRules recursiveSeeds () 2 :=
  .interact (Or.inr ⟨rfl, rfl, rfl⟩) recursive_first_effect recursive_first_effect

theorem nullary_boundary_is_real :
    42 ∈ observations noSeeds [] [nullaryRule] ∧
      ¬ Interaction.Reaches noDeps recursiveRules recursiveEmpty () 42 := by
  constructor
  · rw [nullary_effect_without_components]
    simp
  · exact recursive_empty_seeds_cannot_emit noDeps recursiveRules 42

end SoftwareIsComposable.OneShotBoundary
