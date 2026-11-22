import Mediation

namespace Mediation
variable {n : Nat}

def ReadyAt (g : Graph n) (x : Fin n) : Prop :=
  ∃ s ∈ g.sensors, s.ready ∧ s.node = x

-- A safe repair region contains every changed source and readiness node,
-- and is closed under predecessors in the union of the two snapshots.
structure Cut (old next : Graph n) (inside : Fin n → Bool) : Prop where
  stableEdges : ∀ x y, inside x = false → (Edge old x y ↔ Edge next x y)
  stableReady : ∀ x, inside x = false → (ReadyAt old x ↔ ReadyAt next x)
  noEntry : ∀ x y, inside x = false → (Edge old x y ∨ Edge next x y) →
    inside y = false

theorem Cut.symm {old next : Graph n} {inside : Fin n → Bool}
    (c : Cut old next inside) : Cut next old inside :=
  ⟨fun x y h => (c.stableEdges x y h).symm,
   fun x h => (c.stableReady x h).symm,
   fun x y h e => c.noEntry x y h e.symm⟩

theorem reverse_of_ready {g : Graph n} {x : Fin n}
    (h : ReadyAt g x) : ReverseReached g x := by
  rcases h with ⟨s, hs, ok, rfl⟩
  exact .ready hs ok

theorem retained_forward {old next : Graph n} {inside : Fin n → Bool}
    (cut : Cut old next inside) {x : Fin n}
    (oldReach : ReverseReached old x) (out : inside x = false) :
    ReverseReached next x := by
  induction oldReach with
  | ready hs ok =>
    exact reverse_of_ready ((cut.stableReady _ out).mp ⟨_, hs, ok, rfl⟩)
  | back e _ ih =>
    exact .back ((cut.stableEdges _ _ out).mp e)
      (ih (cut.noEntry _ _ out (.inl e)))

theorem outside_exact {old next : Graph n} {inside : Fin n → Bool}
    (cut : Cut old next inside) {x : Fin n} (out : inside x = false) :
    ReverseReached old x ↔ ReverseReached next x :=
  ⟨fun h => retained_forward cut h out, fun h => retained_forward cut.symm h out⟩

-- Old marks inside the cut are deliberately unavailable. An unsupported
-- cycle in the new graph cannot generate a finite derivation from nothing.
inductive Repair (old next : Graph n) (inside : Fin n → Bool) : Fin n → Prop
  | retain {x} : inside x = false → ReverseReached old x → Repair old next inside x
  | seed {x} : inside x = true → ReadyAt next x → Repair old next inside x
  | back {x y} : inside x = true → Edge next x y →
      Repair old next inside y → Repair old next inside x

theorem repair_sound {old next : Graph n} {inside : Fin n → Bool}
    (cut : Cut old next inside) {x : Fin n} (h : Repair old next inside x) :
    ReverseReached next x := by
  induction h with
  | retain out reach => exact (outside_exact cut out).mp reach
  | seed _ ready => exact reverse_of_ready ready
  | back _ e _ ih => exact .back e ih

theorem repair_complete {old next : Graph n} {inside : Fin n → Bool}
    (cut : Cut old next inside) {x : Fin n} (h : ReverseReached next x) :
    Repair old next inside x := by
  induction h with
  | @ready s hs ok =>
    cases b : inside s.node with
    | false => exact .retain b ((outside_exact cut b).mpr (.ready hs ok))
    | true => exact .seed b ⟨s, hs, ok, rfl⟩
  | @back x y e path ih =>
    cases b : inside x with
    | false => exact .retain b ((outside_exact cut b).mpr (.back e path))
    | true => exact .back b e ih

theorem repair_exact {old next : Graph n} {inside : Fin n → Bool}
    (cut : Cut old next inside) (x : Fin n) :
    Repair old next inside x ↔ Observed next x :=
  ⟨fun h => reverse_sound (repair_sound cut h),
   fun h => repair_complete cut (reverse_complete h)⟩

-- The authoritative delta must name at least every source with changed
-- outbound arcs and every readiness change. Starting with that delta, this
-- is the least predecessor-closed region in the union.
inductive Affected (old next : Graph n) (delta : Fin n → Prop) : Fin n → Prop
  | changed {x} : delta x → Affected old next delta x
  | back {x y} : Edge old x y ∨ Edge next x y →
      Affected old next delta y → Affected old next delta x

theorem affected_least {old next : Graph n} {delta : Fin n → Prop}
    (region : Fin n → Prop)
    (start : ∀ x, delta x → region x)
    (back : ∀ x y, (Edge old x y ∨ Edge next x y) → region y → region x)
    {x : Fin n} (h : Affected old next delta x) : region x := by
  induction h with
  | changed d => exact start _ d
  | back e _ ih => exact back _ _ e ih

theorem cut_of_affected {old next : Graph n} {inside : Fin n → Bool}
    (delta : Fin n → Prop)
    (region : ∀ x, inside x = true ↔ Affected old next delta x)
    (stableEdges : ∀ x y, ¬ delta x → (Edge old x y ↔ Edge next x y))
    (stableReady : ∀ x, ¬ delta x → (ReadyAt old x ↔ ReadyAt next x)) :
    Cut old next inside := by
  have clean : ∀ x, inside x = false → ¬ Affected old next delta x := by
    intro x no h
    have yes := (region x).mpr h
    rw [no] at yes
    cases yes
  exact ⟨fun x y out => stableEdges x y (fun d => clean x out (.changed d)),
    fun x out => stableReady x (fun d => clean x out (.changed d)),
    fun x y out e => by
      cases b : inside y with
      | false => rfl
      | true => exact False.elim (clean x out (.back e ((region y).mp b)))⟩

end Mediation
