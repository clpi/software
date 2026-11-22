import Mediation

namespace MediationControls
open Mediation

def lamp : Sensor 3 := ⟨0,true,true,true⟩
def broken : Sensor 3 := ⟨0,true,false,true⟩
def absent : Sensor 3 := ⟨0,false,true,true⟩
def misleading : Sensor 3 := ⟨0,true,true,false⟩
def full : Graph 3 := ⟨[(2,1),(1,0)], [lamp]⟩
def blank : Graph 3 := ⟨[], [lamp]⟩
def first : Rule 3 := ⟨[0],1⟩
def second : Rule 3 := ⟨[0,1],2⟩
def oracle : Rule 3 := ⟨[],2⟩

theorem two_step : Closure [0] [first, second] (2 : Fin 3) := by
  have zero : Closure [0] [first, second] (0 : Fin 3) := .seed (by decide)
  have one : Closure [0] [first, second] (1 : Fin 3) := by
    apply Closure.fire (r := first) (by decide)
    intro p hp
    change p ∈ [0] at hp
    simp at hp
    exact hp ▸ zero
  apply Closure.fire (r := second) (by decide)
  intro p hp
  change p ∈ [0,1] at hp
  simp at hp
  rcases hp with rfl | rfl
  · exact zero
  · exact one

theorem covered : Observed full (2 : Fin 3) := by
  apply closure_observed full [0] [first,second] _ _ two_step
  · intro x hx
    simp at hx
    subst x
    exact ⟨lamp, by decide, by simp [Sensor.ready, lamp], .here 0⟩
  · intro r hr _
    simp at hr
    rcases hr with rfl | rfl
    · exact Or.inr ⟨0, by decide, by simp [Edge, full, first]⟩
    · exact Or.inr ⟨1, by decide, by simp [Edge, full, second]⟩

theorem empty_arcs_no_path {n : Nat} {ss : List (Sensor n)} {x y : Fin n}
    (p : Path ⟨[],ss⟩ x y) : x = y := by
  cases p with
  | here => rfl
  | step e => exact False.elim (by cases e)

theorem absent_link : ¬ Observed blank (2 : Fin 3) := by
  rintro ⟨s, hs, _, p⟩
  change s ∈ [lamp] at hs
  simp at hs
  subst s
  have eq := empty_arcs_no_path p
  exact (by decide : (2 : Fin 3) ≠ (0 : Fin 3)) eq

theorem not_ready_no_coverage (s : Sensor 3) (NotReady : ¬ s.ready) :
    ¬ Observed ⟨full.edges,[s]⟩ (2 : Fin 3) := by
  rintro ⟨t, ht, h, _⟩
  simp at ht
  subst t
  exact NotReady h

theorem broken_control : ¬ Observed ⟨full.edges,[broken]⟩ (2 : Fin 3) :=
  not_ready_no_coverage broken (by simp [Sensor.ready, broken])

theorem absent_sensor_control : ¬ Observed ⟨full.edges,[absent]⟩ (2 : Fin 3) :=
  not_ready_no_coverage absent (by simp [Sensor.ready, absent])

theorem misleading_control : ¬ Observed ⟨full.edges,[misleading]⟩ (2 : Fin 3) :=
  not_ready_no_coverage misleading (by simp [Sensor.ready, misleading])

theorem nullary_not_automatic : Closure [] [oracle] (2 : Fin 3) ∧
    ¬ Observed blank (2 : Fin 3) := by
  refine ⟨.fire (r := oracle) (by decide) ?_, absent_link⟩
  intro p hp
  cases hp

theorem target_membership_does_not_follow_from_closure (x : Fin 3) :
    ¬ Closure [] ([] : List (Rule 3)) x := by
  intro h
  cases h with
  | seed e => cases e
  | fire e => cases e

end MediationControls
