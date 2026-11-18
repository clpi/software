import Family.Selection

/-!
# Dataflow semantics discharge the `Local` premise

`Local` is the premise every incremental theorem rests on. Here it is proved, not assumed, for
one broad class: a release where each component's behavior is computed from its own code and
the behaviors of the components it declares as dependencies, and from nothing else. That is the
discipline of hermetic builds (Bazel, Nix): a step may read only its declared inputs. Under it
the dependency graph is complete by construction, so `recheck_iff_scratch` and `cone_least`
apply with no further premise about the graph.

`closed_witness_sound` is the checker form: a submitter may propose any set of symbols to
recheck; if the set contains every changed symbol and every dependent of a member, and every
member passes, the whole new release passes. The set is untrusted; only its closure is checked.

What remains trusted: that the real system is a dataflow of this shape (the code really reads
nothing undeclared), and the property `Q` (the spec).
-/
namespace Family.Dataflow

open SoftwareIsIncrementallySafe.OrderedIncrement
open Family.Selection

variable {σ C β : Type}

/-- Evaluate component `s` with `n` levels of dependencies. Undeclared components are never
read: the step sees `d` for them. -/
def run (dep : σ → σ → Bool) (step : σ → C → (σ → β) → β) (d : β) (I : σ → C) :
    Nat → σ → β
  | 0, _ => d
  | n + 1, s => step s (I s) (fun t => if dep s t then run dep step d I n t else d)

def Deps (dep : σ → σ → Bool) : σ → σ → Prop := fun s t => dep s t = true

theorem run_local (dep : σ → σ → Bool) (step : σ → C → (σ → β) → β) (d : β) :
    ∀ n (I I' : σ → C) (s : σ), (∀ t, DepStar (Deps dep) s t → I t = I' t) →
      run dep step d I n s = run dep step d I' n s
  | 0, _, _, _, _ => rfl
  | n + 1, I, I', s, h => by
    simp only [run]
    rw [h s (.refl s)]
    congr 1
    funext t
    by_cases hd : dep s t = true
    · simp only [hd, if_true]
      exact run_local dep step d n I I' t (fun u hu => h u (.step hd hu))
    · simp [hd]

/-- The semantics at a fixed depth bound is `Local` for the declared graph. -/
theorem dataflow_local (dep : σ → σ → Bool) (step : σ → C → (σ → β) → β) (d : β) (n : Nat) :
    Local (Deps dep) (fun I s => run dep step d I n s) :=
  fun I I' s h => run_local dep step d n I I' s h

/-- A closed set contains the cone. -/
theorem cone_sub_closed {deps : σ → σ → Prop} {changed : σ → Bool} (K : σ → Prop)
    (hc : ∀ s, changed s = true → K s) (hd : ∀ s t, deps s t → K t → K s) :
    ∀ s, Cone deps changed s → K s := by
  intro s hs
  obtain ⟨u, hsu, hu⟩ := cone_reach hs
  induction hsu with
  | refl _ => exact hc _ hu
  | step hst _ ih => exact hd _ _ hst (ih (reach_cone ⟨_, by assumption, hu⟩) hu)

/-- Checker form: an untrusted recheck set, verified closed, is enough. -/
theorem closed_witness_sound {deps : σ → σ → Prop} {sem : (σ → C) → σ → β}
    {Q : σ → β → Prop} {I new : σ → C} {changed : σ → Bool} (K : σ → Prop)
    (hc : ∀ s, changed s = true → K s) (hd : ∀ s t, deps s t → K t → K s)
    (hLoc : Local deps sem) (hOld : ∀ s, Q s (sem I s))
    (hK : ∀ s, K s → Q s (sem (update I changed new) s)) :
    ∀ s, Q s (sem (update I changed new) s) :=
  (recheck_iff_scratch deps sem Q I changed new hLoc hOld).mp
    (fun s hs => hK s (cone_sub_closed K hc hd s hs))

/-- Outside a closed set, behavior is literally unchanged: nothing there is re-run. -/
theorem outside_closed_unchanged {deps : σ → σ → Prop} {sem : (σ → C) → σ → β}
    {I new : σ → C} {changed : σ → Bool} (K : σ → Prop)
    (hc : ∀ s, changed s = true → K s) (hd : ∀ s t, deps s t → K t → K s)
    (hLoc : Local deps sem) (s : σ) (hs : ¬ K s) :
    sem (update I changed new) s = sem I s :=
  outside_cone_stable hLoc (fun h => hs (cone_sub_closed K hc hd s h))

end Family.Dataflow
