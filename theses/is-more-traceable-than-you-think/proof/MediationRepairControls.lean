import MediationRepair

namespace MediationRepairControls
open Mediation

def sensor : Sensor 3 := ⟨2, true, true, true⟩
def before : Graph 3 := ⟨[(0,1), (1,0), (1,2)], [sensor]⟩
def after : Graph 3 := ⟨[(0,1), (1,0)], [sensor]⟩

theorem before_cycle_observed : Observed before (0 : Fin 3) :=
  ⟨sensor, by decide, by simp [Sensor.ready, sensor],
    Path.step (y := (1 : Fin 3)) (by simp [Edge, before]) (Path.step (y := (2 : Fin 3)) (by simp [Edge, before, sensor]) (.here _))⟩

theorem after_only_sensor {x : Fin 3} (h : ReverseReached after x) :
    x = (2 : Fin 3) := by
  induction h with
  | ready hs _ =>
    simp [after] at hs
    simp [hs, sensor]
  | back e _ ih =>
    simp [ih, Edge, after] at e

theorem lost_exit_removes_cyclic_mark : ¬ Observed after (0 : Fin 3) := by
  intro h
  exact (by decide : (0 : Fin 3) ≠ 2) (after_only_sensor (reverse_complete h))

end MediationRepairControls
