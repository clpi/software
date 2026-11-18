import SoftwareIsComposable.Profile
import SoftwareIsQuantifiable.Pareto
import SoftwareIsQuantifiable.Interface

open SoftwareIsComposable
open SoftwareIsQuantifiable.Pareto

namespace SoftwareIsIncrementallySafe

def doorStopped : List String → Bool
  | [] => true
  | _ :: rest => doorStopped rest

def door : List String → Bool
  | [] => true
  | e :: rest =>
    if e == "stop" then doorStopped rest
    else if e == "open" then false
    else door rest

def doorProp (t : List String) : Prop := door t = true

theorem doorStopped_true : ∀ t, doorStopped t = true
  | [] => rfl
  | _ :: rest => by simp [doorStopped, doorStopped_true rest]

theorem door_prefix_closed {p rest : List String} (ht : doorProp (p ++ rest)) : doorProp p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    unfold doorProp at ht ⊢
    simp only [List.cons_append, door] at ht ⊢
    cases hstop : a == "stop" with
    | true => simp [hstop, doorStopped_true]
    | false =>
      cases hopen : a == "open" with
      | true => simp [hstop, hopen] at ht
      | false =>
        simp [hstop, hopen] at ht
        exact ih ht

def prefixClosed (P : List String → Prop) : Prop :=
  ∀ t p, P t → p <+: t → P p

theorem door_is_prefixClosed : prefixClosed doorProp := by
  intro t p ht hp
  rcases hp with ⟨rest, rfl⟩
  exact door_prefix_closed ht

structure SpecAuthority where
  traceOK : List String → Bool
  eventOK : Nat → Nat → Bool
  symHigh : Nat → Bool
  obsHigh : Nat → Bool
  boundTime : Nat
  boundCompute : Nat
  obsCost : Nat → Nat
  forbidden : List Nat
  calls : List (Nat × Nat)
  roster : List Nat
  traceAllowed : List String → Prop
  eventAllowed : Nat → Nat → Prop
  traceAgrees : ∀ t, traceOK t = true ↔ traceAllowed t
  eventAgrees : ∀ s b, eventOK s b = true ↔ eventAllowed s b
  tracePrefixClosed : prefixClosed traceAllowed

def gm (sys : Bool → Bool) : Prop :=
  ∀ h1 h2, sys h1 = sys h2

def behaviorsOf (r : Release) : List Nat :=
  r.symbols.flatMap SymbolProfile.behaviors

def ReleaseSafe (spec : SpecAuthority) (prior : PriorQualification Nat)
    (r : Release) (traces : List (List String)) (sys : Bool → Bool) : Prop :=
  prior.qualified ≠ [] ∧
    (∀ b, b ∈ prior.qualified → b ∈ behaviorsOf r) ∧
    (∀ s, s ∈ r.symbols → ∀ b, b ∈ s.behaviors → spec.eventAllowed s.id b) ∧
    prefixClosed spec.traceAllowed ∧
    (∀ t, t ∈ traces → spec.traceAllowed t) ∧
    gm sys

def TaintFree (symHigh : Nat → Bool) (obsHigh : Nat → Bool) (r : Release) : Prop :=
  ∀ s, s ∈ r.symbols → symHigh s.id = false → ∀ b, b ∈ s.behaviors → obsHigh b = false

theorem nothing_refused (spec : SpecAuthority) (prior : PriorQualification Nat)
    (b : Nat) (hb : b ∈ prior.qualified) (traces : List (List String)) (sys : Bool → Bool) :
    ¬ ReleaseSafe spec prior ⟨[]⟩ traces sys := by
  intro h
  have hmem := h.2.1 b hb
  simp [behaviorsOf] at hmem

def emptyBehaviorRelease (id : Nat) : Release :=
  ⟨[{ id := id, behaviors := [], costs := [] }]⟩

theorem empty_behaviors_refused (spec : SpecAuthority) (b : Nat) (id : Nat)
    (traces : List (List String)) (sys : Bool → Bool) :
    ¬ ReleaseSafe spec ⟨[b]⟩ (emptyBehaviorRelease id) traces sys := by
  intro h
  rcases h with ⟨_, hsub, _⟩
  have hb : b ∈ behaviorsOf (emptyBehaviorRelease id) := hsub b (by simp)
  simp [behaviorsOf, emptyBehaviorRelease] at hb

def allowedTrace (A : String → Prop) (t : List String) : Prop :=
  ∀ o, o ∈ t → A o

theorem allowedTrace_swap (A : String → Prop) (a b : String) :
    allowedTrace A [a, b] ↔ allowedTrace A [b, a] := by
  constructor <;> intro h o ho <;> apply h <;> simp at ho ⊢ <;> exact ho.symm

def noiseSys : Bool → Bool := fun _ => false

def leakSys : Bool → Bool := fun s => s

theorem noise_gm : gm noiseSys := fun _ _ => rfl

theorem leak_not_gm : ¬ gm leakSys := by
  intro h
  have := h true false
  simp [leakSys] at this

def doorDataTraceOK : List String → Bool := door

def doorEventOK : Nat → Nat → Bool := fun _ b => b == 0 || b == 1

theorem door_trace_agrees (t : List String) : doorDataTraceOK t = true ↔ doorProp t := Iff.rfl

theorem door_event_agrees (s b : Nat) : doorEventOK s b = true ↔ b = 0 ∨ b = 1 := by
  simp [doorEventOK, Bool.or_eq_true, beq_iff_eq]

def doorAuthority : SpecAuthority where
  traceOK := door
  eventOK := doorEventOK
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10
  obsCost := fun _ => 0
  forbidden := []
  calls := []
  roster := [50]
  traceAllowed := doorProp
  eventAllowed := fun _ b => b = 0 ∨ b = 1
  traceAgrees := door_trace_agrees
  eventAgrees := door_event_agrees
  tracePrefixClosed := by
    intro t p ht hp
    exact door_is_prefixClosed t p ht hp

def stopOpenRelease : Release :=
  ⟨[{ id := 50, behaviors := [0], costs := [] }]⟩

def doorPrior : PriorQualification Nat := ⟨[0]⟩

theorem door_releaseSafe_stop_open :
    ReleaseSafe doorAuthority doorPrior stopOpenRelease [["stop", "open"]] noiseSys := by
  refine ⟨?_, ?_, ?_, ?_, ?_, noise_gm⟩
  · simp [doorPrior]
  · intro b hb
    simp [doorPrior] at hb
    subst hb
    simp [behaviorsOf, stopOpenRelease]
  · intro s hs b hb
    simp [stopOpenRelease] at hs hb
    subst hs
    simp [doorAuthority] at hb ⊢
    subst hb
    simp
  · exact doorAuthority.tracePrefixClosed
  · intro t ht
    simp at ht
    subst ht
    simp [doorAuthority, doorProp, door, doorStopped]

theorem door_not_releaseSafe_open_stop :
    ¬ ReleaseSafe doorAuthority doorPrior stopOpenRelease [["open", "stop"]] noiseSys := by
  intro h
  have ht := h.2.2.2.2.1 ["open", "stop"] (by simp)
  simp [doorAuthority, doorProp, door] at ht

theorem f1_releaseSafe_distinguishes :
    ReleaseSafe doorAuthority doorPrior stopOpenRelease [["stop", "open"]] noiseSys ∧
      ¬ ReleaseSafe doorAuthority doorPrior stopOpenRelease [["open", "stop"]] noiseSys :=
  ⟨door_releaseSafe_stop_open, door_not_releaseSafe_open_stop⟩

theorem c5_swap_does_not_yield_releaseSafe :
    allowedTrace (fun _ => True) ["open", "stop"] ∧
      allowedTrace (fun _ => True) ["stop", "open"] ∧
      ¬ ReleaseSafe doorAuthority doorPrior stopOpenRelease [["open", "stop"]] noiseSys := by
  refine ⟨?_, ?_, door_not_releaseSafe_open_stop⟩
  · intro o ho
    simp at ho
    cases ho <;> trivial
  · intro o ho
    simp at ho
    cases ho <;> trivial

theorem leak_not_releaseSafe :
    ¬ ReleaseSafe doorAuthority doorPrior stopOpenRelease [["stop", "open"]] leakSys := by
  intro h
  exact leak_not_gm h.2.2.2.2.2

theorem f2_two_run :
    ¬ ReleaseSafe doorAuthority doorPrior stopOpenRelease [["stop", "open"]] leakSys ∧
      ReleaseSafe doorAuthority doorPrior stopOpenRelease [["stop", "open"]] noiseSys :=
  ⟨leak_not_releaseSafe, door_releaseSafe_stop_open⟩

def profileOf (f : Bool → Bool → Prop) : Bool → Prop :=
  fun o => ∃ s, f s o

def leakBit : Bool → Bool → Prop := fun s o => o = s

def noiseBit : Bool → Bool → Prop := fun _ _ => True

theorem same_profile : profileOf leakBit = profileOf noiseBit := by
  funext o
  apply propext
  exact ⟨fun _ => ⟨o, trivial⟩, fun _ => ⟨o, rfl⟩⟩

theorem releaseLe_keeps_incumbent
    {Symbol Measure : Type} (space : SoftwareIsQuantifiable.Interface.MeasureSpace Measure)
    (candidate incumbent : SoftwareIsQuantifiable.Interface.Release Symbol Measure)
    (h : SoftwareIsQuantifiable.Interface.releaseLe space candidate incumbent) :
    ∀ q, q ∈ incumbent →
      ∃ p, p ∈ candidate ∧ SoftwareIsQuantifiable.Interface.noWorse space p q :=
  h.2.2.2.2

#print axioms nothing_refused
#print axioms empty_behaviors_refused
#print axioms f1_releaseSafe_distinguishes
#print axioms c5_swap_does_not_yield_releaseSafe
#print axioms leak_not_gm
#print axioms f2_two_run
#print axioms same_profile
#print axioms releaseLe_keeps_incumbent
#print axioms door_is_prefixClosed

end SoftwareIsIncrementallySafe
