
/-!
# Incremental recheck over ordered traces and two-run noninterference

This module closes the two gaps left by `ReleaseSafe` and `NI` in
`Increment.lean` and `Security.lean`:

* those predicates see a release as a set of observations, so event order is
  invisible (`allow_list_ignores_order`) and a leak and random noise get the
  same verdict;
* `RunAdmission` checks ordered traces and possibilistic noninterference, but
  only as a full re-check of one finite model, with no incremental theorem.

Here a release assigns code to symbols, and its semantics gives every symbol a
behavior: for each input, a set of ordered traces. The headline results say
that rechecking only the dependency cone of a change is equivalent to
rechecking everything, for

* prefix-closed trace safety (safety in the Alpern and Schneider sense, over
  finite ordered traces), and
* noninterference in the two-run sense (Goguen and Meseguer, possibilistic
  form as in McCullough): low-equivalent inputs yield the same set of low
  views.

## Premise, stated once

`Local deps sem`: the behavior of a symbol is determined by the code of the
symbols in its dependency closure. This is what "the dependency graph is
complete" means semantically. It allows cycles and arbitrary (emergent)
interaction among a symbol's dependencies; it does not allow behavior to
change through a path the graph does not contain (data, configuration,
environment, timing outside the model). It is a premise and is never derived.

## What is false

* Rechecking only the changed symbols, not their dependents, is unsound for
  noninterference, even when the new code refines the old one at every symbol
  (`naive_changed_only_false`, `refinement_does_not_preserve_NI`). Trace
  safety does survive refinement (`refinement_preserves_traceSafe`). This is
  the refinement paradox of information flow.
* So the cone recheck below rechecks dependents too. With that, no per-component
  noninterference or flow-typing condition is needed: the theorem is generic in
  the per-symbol property, hyperproperties included (`recheck_iff_scratch`).
-/

namespace SoftwareIsIncrementallySafe.OrderedIncrement

open Classical

/-- The cone of a change: symbols that depend, possibly indirectly, on a changed
symbol (same shape as `SoftwareIsComposable.Cone`, restated so this module
needs only Lean core and builds on any branch). -/
inductive Cone {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) : σ → Prop where
  | root {s : σ} : changed s = true → Cone deps changed s
  | step {s t : σ} : deps s t → Cone deps changed t → Cone deps changed s

theorem not_cone_not_changed {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool} {s : σ}
    (h : ¬ Cone deps changed s) : changed s = false := by
  cases hc : changed s with
  | false => rfl
  | true => exact (h (Cone.root hc)).elim

/-! ## 1. Releases, dependency closure, and the locality premise -/

/-- Reflexive-transitive closure of the dependency relation:
`DepStar deps s t` means `s` depends, possibly indirectly, on `t`. -/
inductive DepStar {σ : Type} (deps : σ → σ → Prop) : σ → σ → Prop where
  | refl (s : σ) : DepStar deps s s
  | step {s t u : σ} : deps s t → DepStar deps t u → DepStar deps s u

/-- PREMISE. The semantics of symbol `s` depends only on the code of the symbols
in its dependency closure. `β` is whatever a symbol's behavior is (a set of
traces per input below; a finite `RunAdmission.Model` in section 5). -/
def Local {σ C β : Type} (deps : σ → σ → Prop) (sem : (σ → C) → σ → β) : Prop :=
  ∀ (I I' : σ → C) (s : σ), (∀ t, DepStar deps s t → I t = I' t) → sem I s = sem I' s

/-- The new release: changed symbols get new code, the rest keep theirs. -/
def update {σ C : Type} (I : σ → C) (changed : σ → Bool) (new : σ → C) : σ → C :=
  fun s => if changed s then new s else I s

theorem update_unchanged {σ C : Type} {I : σ → C} {changed : σ → Bool} {new : σ → C}
    {s : σ} (h : changed s = false) : update I changed new s = I s := by
  simp [update, h]

/-- A symbol outside the cone (reverse dependency closure of the change) has no
changed symbol anywhere in its dependency closure. -/
theorem not_cone_closure_unchanged {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool}
    {s : σ} (h : ¬ Cone deps changed s) : ∀ t, DepStar deps s t → changed t = false := by
  intro t hst
  revert h
  induction hst with
  | refl _ => exact fun h => not_cone_not_changed h
  | step hd _ ih => exact fun h => ih (fun hc => h (Cone.step hd hc))

theorem outside_cone_stable {σ C β : Type} {deps : σ → σ → Prop} {sem : (σ → C) → σ → β}
    {I : σ → C} {changed : σ → Bool} {new : σ → C} {s : σ}
    (hLoc : Local deps sem) (h : ¬ Cone deps changed s) :
    sem (update I changed new) s = sem I s :=
  hLoc _ _ s (fun t ht => update_unchanged (not_cone_closure_unchanged h t ht))

/-! ## 2. The generic incremental theorem

`Q s b` is any property of symbol `s`'s whole behavior `b`. Nothing about `Q` is
assumed: it may relate several runs (a hyperproperty). -/

theorem recheck_iff_scratch {σ C β : Type} (deps : σ → σ → Prop) (sem : (σ → C) → σ → β)
    (Q : σ → β → Prop) (I : σ → C) (changed : σ → Bool) (new : σ → C)
    (hLoc : Local deps sem) (hOld : ∀ s, Q s (sem I s)) :
    (∀ s, Cone deps changed s → Q s (sem (update I changed new) s)) ↔
      (∀ s, Q s (sem (update I changed new) s)) := by
  constructor
  · intro hc s
    by_cases h : Cone deps changed s
    · exact hc s h
    · rw [outside_cone_stable hLoc h]
      exact hOld s
  · intro h s _
    exact h s

/-- A sequence of changes, each accepted by rechecking only its own cone. -/
def applyAll {σ C : Type} (I : σ → C) : List ((σ → Bool) × (σ → C)) → (σ → C)
  | [] => I
  | (ch, nw) :: rest => applyAll (update I ch nw) rest

def ChainAccepted {σ C β : Type} (deps : σ → σ → Prop) (sem : (σ → C) → σ → β)
    (Q : σ → β → Prop) : (σ → C) → List ((σ → Bool) × (σ → C)) → Prop
  | _, [] => True
  | I, (ch, nw) :: rest =>
      (∀ s, Cone deps ch s → Q s (sem (update I ch nw) s)) ∧
        ChainAccepted deps sem Q (update I ch nw) rest

theorem chain_recheck {σ C β : Type} (deps : σ → σ → Prop) (sem : (σ → C) → σ → β)
    (Q : σ → β → Prop) (hLoc : Local deps sem) :
    ∀ (ds : List ((σ → Bool) × (σ → C))) (I : σ → C),
      (∀ s, Q s (sem I s)) → ChainAccepted deps sem Q I ds →
        ∀ s, Q s (sem (applyAll I ds) s)
  | [], _, hOld, _ => hOld
  | (ch, nw) :: rest, I, hOld, ⟨hCone, hRest⟩ =>
      chain_recheck deps sem Q hLoc rest (update I ch nw)
        ((recheck_iff_scratch deps sem Q I ch nw hLoc hOld).mp hCone) hRest

/-! ## 3. Ordered-trace safety and two-run noninterference -/

/-- A behavior: for each input, the set of finite ordered traces it can produce. -/
abbrev Beh (ι ε : Type) := ι → List ε → Prop

/-- Safety over finite traces: closed under prefixes, so every violation is
witnessed by a finite bad prefix. -/
def PrefixClosed {ε : Type} (P : List ε → Prop) : Prop :=
  ∀ t p, P t → p <+: t → P p

def TraceSafe {ι ε : Type} (P : List ε → Prop) (b : Beh ι ε) : Prop :=
  ∀ i t, b i t → P t

/-- With a prefix-closed `P`, every prefix of every run is safe too, so a monitor
can reject a run at the first bad prefix. -/
theorem traceSafe_prefixes {ι ε : Type} {P : List ε → Prop} (hP : PrefixClosed P)
    {b : Beh ι ε} (h : TraceSafe P b) : ∀ i t p, b i t → p <+: t → P p :=
  fun i t p ht hp => hP t p (h i t ht) hp

/-- What an observer may distinguish: which inputs it cannot tell apart, and
what part of a trace it sees. -/
structure Flow (ι ε : Type) where
  lowEq : ι → ι → Prop
  lowView : List ε → List ε

/-- Possibilistic noninterference, a property of pairs of runs: whatever low
view one input can produce, every low-equivalent input can produce too. -/
def NI {ι ε : Type} (F : Flow ι ε) (b : Beh ι ε) : Prop :=
  ∀ i j, F.lowEq i j → ∀ t, b i t → ∃ t', b j t' ∧ F.lowView t' = F.lowView t

/-- Per-symbol specification. The safety predicate must be a safety property. -/
structure Spec (σ ι ε : Type) where
  safe : σ → List ε → Prop
  safe_prefixClosed : ∀ s, PrefixClosed (safe s)
  flow : σ → Flow ι ε

def Good {σ ι ε : Type} (S : Spec σ ι ε) (s : σ) (b : Beh ι ε) : Prop :=
  TraceSafe (S.safe s) b ∧ NI (S.flow s) b

/-- The whole release: every symbol is safe and noninterfering. -/
def ReleaseGood {σ C ι ε : Type} (S : Spec σ ι ε) (sem : (σ → C) → σ → Beh ι ε)
    (I : σ → C) : Prop :=
  ∀ s, Good S s (sem I s)

/-- What the incremental checker inspects: only symbols in the cone. -/
def ConeGood {σ C ι ε : Type} (S : Spec σ ι ε) (deps : σ → σ → Prop)
    (sem : (σ → C) → σ → Beh ι ε) (I : σ → C) (changed : σ → Bool) (new : σ → C) : Prop :=
  ∀ s, Cone deps changed s → Good S s (sem (update I changed new) s)

/-- HEADLINE. Given a sound dependency graph (`Local`) and a good old release,
rechecking the cone of a change for ordered-trace safety and two-run
noninterference is equivalent to rechecking the whole new release. -/
theorem ordered_incremental_iff_scratch {σ C ι ε : Type} (S : Spec σ ι ε)
    (deps : σ → σ → Prop) (sem : (σ → C) → σ → Beh ι ε)
    (I : σ → C) (changed : σ → Bool) (new : σ → C)
    (hLoc : Local deps sem) (hOld : ReleaseGood S sem I) :
    ConeGood S deps sem I changed new ↔ ReleaseGood S sem (update I changed new) :=
  recheck_iff_scratch deps sem (Good S) I changed new hLoc hOld

theorem ordered_safety_preserved {σ C ι ε : Type} (S : Spec σ ι ε)
    (deps : σ → σ → Prop) (sem : (σ → C) → σ → Beh ι ε)
    (I : σ → C) (changed : σ → Bool) (new : σ → C)
    (hLoc : Local deps sem) (hOld : ReleaseGood S sem I)
    (hCone : ConeGood S deps sem I changed new) :
    ∀ s i t, sem (update I changed new) s i t → S.safe s t :=
  fun s => ((ordered_incremental_iff_scratch S deps sem I changed new hLoc hOld).mp hCone s).1

theorem noninterference_preserved {σ C ι ε : Type} (S : Spec σ ι ε)
    (deps : σ → σ → Prop) (sem : (σ → C) → σ → Beh ι ε)
    (I : σ → C) (changed : σ → Bool) (new : σ → C)
    (hLoc : Local deps sem) (hOld : ReleaseGood S sem I)
    (hCone : ConeGood S deps sem I changed new) :
    ∀ s, NI (S.flow s) (sem (update I changed new) s) :=
  fun s => ((ordered_incremental_iff_scratch S deps sem I changed new hLoc hOld).mp hCone s).2

/-- The same over a sequence of releases. -/
theorem ordered_chain {σ C ι ε : Type} (S : Spec σ ι ε)
    (deps : σ → σ → Prop) (sem : (σ → C) → σ → Beh ι ε) (hLoc : Local deps sem)
    (ds : List ((σ → Bool) × (σ → C))) (I : σ → C)
    (hOld : ReleaseGood S sem I) (hAcc : ChainAccepted deps sem (Good S) I ds) :
    ReleaseGood S sem (applyAll I ds) :=
  chain_recheck deps sem (Good S) hLoc ds I hOld hAcc

/-! ## 4. What is false: the changed-only shortcut and refinement -/

/-- Trace safety survives refinement (fewer runs). -/
theorem refinement_preserves_traceSafe {ι ε : Type} (P : List ε → Prop) {b b' : Beh ι ε}
    (hR : ∀ i t, b' i t → b i t) (h : TraceSafe P b) : TraceSafe P b' :=
  fun i t ht => h i t (hR i t ht)

/-- `leak` outputs the secret bit; `noise` outputs either bit whatever the secret. -/
def leak : Beh Bool Bool := fun i t => t = [i]
def noise : Beh Bool Bool := fun _ t => t = [false] ∨ t = [true]

/-- The observer sees the whole trace and cannot distinguish any inputs. -/
def openFlow : Flow Bool Bool := ⟨fun _ _ => True, id⟩

theorem leak_not_NI : ¬ NI openFlow leak := by
  intro h
  obtain ⟨t', ht', hv⟩ := h true false trivial [true] rfl
  simp only [leak] at ht'
  subst ht'
  simp [openFlow] at hv

theorem noise_NI : NI openFlow noise :=
  fun _ _ _ t ht => ⟨t, by cases ht <;> simp_all [noise], rfl⟩

theorem leak_refines_noise : ∀ i t, leak i t → noise i t := by
  intro i t h
  cases i <;> simp_all [leak, noise]

/-- The refinement paradox: noninterference is not preserved by refinement. -/
theorem refinement_does_not_preserve_NI :
    ¬ ∀ (b b' : Beh Bool Bool), (∀ i t, b' i t → b i t) → NI openFlow b → NI openFlow b' :=
  fun h => leak_not_NI (h noise leak leak_refines_noise noise_NI)

/-- Two symbols: `app` passes `lib`'s output to a low observer. -/
inductive Sym where
  | lib
  | app
  deriving DecidableEq

def symDeps : Sym → Sym → Prop := fun a b => a = .app ∧ b = .lib

def passSem : (Sym → Beh Bool Bool) → Sym → Beh Bool Bool
  | I, .lib => I .lib
  | I, .app => I .lib

theorem passSem_local : Local symDeps passSem := by
  intro I I' s h
  cases s with
  | lib => exact h .lib (DepStar.refl _)
  | app => exact h .lib (DepStar.step ⟨rfl, rfl⟩ (DepStar.refl _))

/-- `lib`'s output is internal (empty low view); `app`'s output is public. -/
def passSpec : Spec Sym Bool Bool where
  safe := fun _ _ => True
  safe_prefixClosed := fun _ _ _ _ _ => trivial
  flow
    | .lib => ⟨fun _ _ => True, fun _ => []⟩
    | .app => openFlow

def oldCode : Sym → Beh Bool Bool := fun _ => noise
def newCode : Sym → Beh Bool Bool := fun _ => leak
def libChanged : Sym → Bool := fun s => decide (s = .lib)

theorem old_release_good : ReleaseGood passSpec passSem oldCode := by
  intro s
  refine ⟨fun _ _ _ => trivial, ?_⟩
  cases s with
  | lib => exact fun _ _ _ t ht => ⟨t, ht, rfl⟩
  | app => exact noise_NI

/-- Rechecking only the changed symbol accepts the change. -/
theorem changed_only_accepts :
    ∀ s, libChanged s = true → Good passSpec s (passSem (update oldCode libChanged newCode) s) := by
  intro s hs
  cases s with
  | app => simp [libChanged] at hs
  | lib =>
    exact ⟨fun _ _ _ => trivial, fun _ j _ _ _ =>
      ⟨[j], by simp [passSem, update, libChanged, newCode, leak], rfl⟩⟩

/-- But the new release leaks through `app`. -/
theorem new_release_leaks :
    ¬ NI (passSpec.flow .app) (passSem (update oldCode libChanged newCode) .app) := by
  have : passSem (update oldCode libChanged newCode) .app = leak := by
    funext i t
    simp [passSem, update, libChanged, newCode]
  rw [this]
  exact leak_not_NI

/-- Every symbol's new behavior refines its old one, so refinement does not help. -/
theorem new_refines_old :
    ∀ s i t, passSem (update oldCode libChanged newCode) s i t → passSem oldCode s i t := by
  intro s i t h
  cases s <;> simp [passSem, update, libChanged, newCode, oldCode] at h ⊢ <;>
    exact leak_refines_noise i t h

/-- DISPROVEN: "a sound graph, a good old release, and a passing check of the
changed symbols imply a good new release". Kernel-checked counterexample. -/
theorem naive_changed_only_false :
    ¬ ∀ (sem : (Sym → Beh Bool Bool) → Sym → Beh Bool Bool)
        (I new : Sym → Beh Bool Bool) (changed : Sym → Bool),
        Local symDeps sem → ReleaseGood passSpec sem I →
        (∀ s, changed s = true → Good passSpec s (sem (update I changed new) s)) →
        ReleaseGood passSpec sem (update I changed new) := by
  intro h
  exact new_release_leaks
    (h passSem oldCode newCode libChanged passSem_local old_release_good changed_only_accepts .app).2

/-- The cone recheck catches it: `app` is in the cone and fails. -/
theorem cone_recheck_refuses : ¬ ConeGood passSpec symDeps passSem oldCode libChanged newCode :=
  fun h => new_release_leaks (h .app (Cone.step ⟨rfl, rfl⟩ (Cone.root (by simp [libChanged])))).2

/-- The premise is load-bearing. Drop the `app → lib` edge: the cone of the
change is just `lib`, the cone check passes, and the new release still leaks
through `app` (`new_release_leaks`). This is R1 from the reaudit, now inside
the ordered and relational model: whoever supplies the graph carries the
burden. -/
theorem missing_edge_cone_passes :
    ConeGood passSpec (fun _ _ => False) passSem oldCode libChanged newCode := by
  intro s hc
  cases hc with
  | root h => exact changed_only_accepts s h
  | step hd _ => exact hd.elim

theorem missing_edge_not_local : ¬ Local (fun _ _ => False : Sym → Sym → Prop) passSem := by
  intro h
  have hEq := h oldCode (update oldCode libChanged newCode) .app (by
    intro t ht
    cases ht with
    | refl => simp [update, libChanged]
    | step hd _ => exact hd.elim)
  have h2 := congrFun (congrFun hEq true) [false]
  simp [passSem, update, libChanged, oldCode, newCode, noise, leak] at h2

/-! ### C5 in the abstract model: order matters

`door` replays `sensor`'s runs and must never open before stopping. Swapping
the order of the same two events is refused by the cone recheck, while the two
releases have exactly the same set of observed events, which is all the old
`allowedTrace` and `ReleaseSafe` could see. -/

def doorOK : Bool → List String → Bool
  | _, [] => true
  | stopped, e :: es =>
    if e == "stop" then doorOK true es
    else if e == "open" then stopped && doorOK stopped es
    else doorOK stopped es

theorem doorOK_prefix (b : Bool) (p r : List String) :
    doorOK b (p ++ r) = true → doorOK b p = true := by
  induction p generalizing b with
  | nil => intro _; rfl
  | cons e es ih =>
    intro h
    simp only [List.cons_append, doorOK] at h ⊢
    split at h
    · rename_i he; simp only [he, if_true]; exact ih _ h
    · rename_i he
      simp only [he, if_false]
      split at h
      · rename_i ho
        simp only [ho, if_true, Bool.and_eq_true] at h ⊢
        simp only [Bool.false_eq_true, if_false, Bool.and_eq_true]
        exact ⟨h.1, ih _ h.2⟩
      · rename_i ho
        simp only [ho, if_false]
        exact ih _ h

theorem doorOK_prefixClosed : PrefixClosed (fun t : List String => doorOK false t = true) := by
  intro t p ht hp
  obtain ⟨r, hr⟩ := hp
  subst hr
  exact doorOK_prefix false p r ht

inductive DoorSym where
  | sensor
  | door
  deriving DecidableEq

def doorDepsP : DoorSym → DoorSym → Prop := fun a b => a = .door ∧ b = .sensor

def doorSemP : (DoorSym → Beh Unit String) → DoorSym → Beh Unit String
  | I, .sensor => I .sensor
  | I, .door => I .sensor

theorem doorSemP_local : Local doorDepsP doorSemP := by
  intro I I' s h
  cases s with
  | sensor => exact h .sensor (DepStar.refl _)
  | door => exact h .sensor (DepStar.step ⟨rfl, rfl⟩ (DepStar.refl _))

def doorSpec : Spec DoorSym Unit String where
  safe
    | .sensor => fun _ => True
    | .door => fun t => doorOK false t = true
  safe_prefixClosed
    | .sensor => fun _ _ _ _ => trivial
    | .door => doorOK_prefixClosed
  flow := fun _ => ⟨fun _ _ => True, id⟩

def stopOpen : DoorSym → Beh Unit String := fun _ _ t => t = ["stop", "open"]
def openStop : DoorSym → Beh Unit String := fun _ _ t => t = ["open", "stop"]
def sensorChanged : DoorSym → Bool := fun s => decide (s = .sensor)

theorem door_old_good : ReleaseGood doorSpec doorSemP stopOpen := by
  intro s
  refine ⟨?_, fun _ _ _ t ht => ⟨t, ht, rfl⟩⟩
  intro _ t ht
  cases s <;> simp only [doorSemP, stopOpen] at ht <;> subst ht <;> simp [doorSpec, doorOK]

theorem door_reordered_refused :
    ¬ ConeGood doorSpec doorDepsP doorSemP stopOpen sensorChanged openStop := by
  intro h
  have hd := (h .door (Cone.step ⟨rfl, rfl⟩ (Cone.root (by simp [sensorChanged])))).1 ()
    ["open", "stop"] (by simp [doorSemP, update, sensorChanged, openStop])
  simp [doorSpec, doorOK] at hd

theorem door_same_events (o : String) :
    (∃ t, stopOpen .door () t ∧ o ∈ t) ↔ (∃ t, openStop .door () t ∧ o ∈ t) := by
  simp [stopOpen, openStop, or_comm]

end SoftwareIsIncrementallySafe.OrderedIncrement

#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.recheck_iff_scratch
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.ordered_incremental_iff_scratch
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.ordered_safety_preserved
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.noninterference_preserved
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.ordered_chain
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.naive_changed_only_false
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.refinement_does_not_preserve_NI
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.cone_recheck_refuses
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.missing_edge_not_local
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.door_reordered_refused
#print axioms SoftwareIsIncrementallySafe.OrderedIncrement.doorOK_prefixClosed
