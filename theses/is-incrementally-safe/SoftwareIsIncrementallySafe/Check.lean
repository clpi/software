import SoftwareIsIncrementallySafe.Model
import SoftwareIsIncrementallySafe.Cone
import OptimalityInterface

open SoftwareIsComposable
open SoftwareIsQuantifiable.Pareto

namespace SoftwareIsIncrementallySafe

inductive CheckVerdict where
  | accept
  | refuse (symbol : Nat)
  deriving DecidableEq, Repr

structure Patch where
  symbol : Nat
  behaviors : List Nat
  trace : List String
  sys : Bool → Bool
  deps : List (Nat × Nat)
  symHigh : Nat → Bool
  obsHigh : Nat → Bool
  boundTime : Nat
  boundCompute : Nat

def releaseOf (p : Patch) : Release :=
  ⟨[{ id := p.symbol, behaviors := p.behaviors, costs := [] }]⟩

def gmB (sys : Bool → Bool) : Bool :=
  sys true == sys false

theorem gmB_iff (sys : Bool → Bool) : gmB sys = true ↔ gm sys := by
  constructor
  · intro h h1 h2
    have heq : sys true = sys false := beq_iff_eq.mp h
    cases h1 <;> cases h2
    · rfl
    · exact heq.symm
    · exact heq
    · rfl
  · intro h
    exact beq_iff_eq.mpr (h true false)

def changedCost (spec : SpecAuthority) (p : Patch) : Nat :=
  p.behaviors.foldl (fun n b => n + spec.obsCost b) 0

def direct (calls : List (Nat × Nat)) (s : Nat) : List Nat :=
  (calls.filter (fun e => e.fst == s)).map Prod.snd

def collect (calls : List (Nat × Nat)) (beh : Nat → List Nat) :
    List Nat → List Nat → Nat → List Nat
  | [], _, _ => []
  | _, _, 0 => []
  | s :: rest, seen, n + 1 =>
    if seen.contains s then collect calls beh rest seen n
    else beh s ++ collect calls beh (direct calls s ++ rest) (s :: seen) n

def reached (spec : SpecAuthority) (beh : Nat → List Nat) (s : Nat) : List Nat :=
  collect spec.calls beh [s] [] (spec.roster.length + spec.calls.length + 2)

def callStrings (calls : List (Nat × Nat)) : List (String × String) :=
  calls.map fun e => (toString e.fst, toString e.snd)

def affected (spec : SpecAuthority) (seed s : Nat) : Bool :=
  (coneExecOf (callStrings spec.calls) [toString seed]).contains (toString s)

def behOf (p : Patch) (s : Nat) : List Nat :=
  if s == p.symbol then p.behaviors else []

def disallowed (spec : SpecAuthority) (p : Patch) (s : Nat) : Bool :=
  (reached spec (behOf p) s).any (fun b => !(spec.eventOK s b))

def coneViolator (spec : SpecAuthority) (p : Patch) : Option Nat :=
  spec.roster.find? fun s => affected spec p.symbol s && s != p.symbol && disallowed spec p s

def symbolAdmitted (spec : SpecAuthority) (prior : PriorQualification Nat) (p : Patch) : Bool :=
  decide (prior.qualified ≠ []) &&
    noQualifiedBehaviorLost prior ⟨p.behaviors⟩ &&
    p.behaviors.all (spec.eventOK p.symbol) &&
    spec.traceOK p.trace &&
    gmB p.sys &&
    !(spec.symHigh p.symbol == false && p.behaviors.any spec.obsHigh) &&
    !(spec.forbidden.contains p.symbol && !p.behaviors.isEmpty) &&
    (decide (changedCost spec p ≤ spec.boundTime) &&
      decide (changedCost spec p ≤ spec.boundCompute))

def check (spec : SpecAuthority) (prior : PriorQualification Nat) (p : Patch) : CheckVerdict :=
  if symbolAdmitted spec prior p = false then
    .refuse p.symbol
  else
    match coneViolator spec p with
    | some s => .refuse s
    | none => .accept

theorem and_true_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => nomatch h

theorem and_true_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => nomatch h
  | true =>
    cases b with
    | true => rfl
    | false => nomatch h

theorem not_eq_true_false {a : Bool} (h : (!a) = true) : a = false := by
  cases a with
  | false => rfl
  | true => nomatch h

theorem all_true_mem {p : Nat → Bool} {l : List Nat} (h : l.all p = true) {a : Nat}
    (ha : a ∈ l) : p a = true :=
  (List.all_eq_true.mp h) a ha

theorem any_false_mem {p : Nat → Bool} {l : List Nat} (h : l.any p = false) {a : Nat}
    (ha : a ∈ l) : p a = false := by
  have hne : p a ≠ true := (List.any_eq_false.mp h) a ha
  cases hp : p a with
  | false => rfl
  | true => exact absurd hp hne

theorem f4_checker_sound (spec : SpecAuthority) (prior : PriorQualification Nat) (p : Patch)
    (h : check spec prior p = .accept) :
    ReleaseSafe spec prior (releaseOf p) [p.trace] p.sys ∧
      TaintFree spec.symHigh spec.obsHigh (releaseOf p) := by
  cases hadm : symbolAdmitted spec prior p with
  | false =>
    rw [check, hadm] at h
    nomatch h
  | true =>
    cases hv : coneViolator spec p with
    | some s =>
      rw [check, hadm, hv] at h
      nomatch h
    | none =>
      simp only [symbolAdmitted, Bool.and_eq_true] at hadm
      rcases hadm with ⟨⟨⟨⟨⟨⟨⟨hne, hkeepB⟩, hallowB⟩, htraceB⟩, hgmB⟩, htaintB⟩, _⟩, _⟩
      have hkeep := (noQualifiedBehaviorLost_iff).mp hkeepB
      have hsub : ∀ b, b ∈ p.behaviors → spec.eventAllowed p.symbol b := by
        intro b hb
        exact (spec.eventAgrees p.symbol b).mp (all_true_mem hallowB hb)
      have htaint : (spec.symHigh p.symbol == false && p.behaviors.any spec.obsHigh) = false :=
        not_eq_true_false htaintB
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_, ?_, spec.tracePrefixClosed, ?_, (gmB_iff p.sys).mp hgmB⟩
        · exact decide_eq_true_iff.mp hne
        · intro b hb
          have hmem := hkeep b hb
          simp [behaviorsOf, releaseOf] at hmem ⊢
          exact hmem
        · intro s hs b hb
          simp [releaseOf] at hs hb
          subst hs
          exact hsub b hb
        · intro t ht
          simp at ht
          subst ht
          exact (spec.traceAgrees p.trace).mp htraceB
      · intro s hs hlow b hb
        simp [releaseOf] at hs
        subst hs
        cases hsym : spec.symHigh p.symbol with
        | true =>
          rw [hsym] at hlow
          cases hlow
        | false =>
          have hobs : p.behaviors.any spec.obsHigh = false := by
            have hnot : (spec.symHigh p.symbol == false) = true := by simp [hsym]
            rw [hnot, Bool.true_and] at htaint
            exact htaint
          exact any_false_mem hobs hb

def plainSys : Bool → Bool := noiseSys

def basePatch (symbol : Nat) (behaviors : List Nat) (trace : List String) : Patch where
  symbol := symbol
  behaviors := behaviors
  trace := trace
  sys := plainSys
  deps := []
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 0
  boundCompute := 0

def nothingPatch : Patch := basePatch 40 [] ["stop"]

def nothingAuth : SpecAuthority :=
  { doorAuthority with roster := [40] }

theorem c4_check_refuses :
    check nothingAuth ⟨[1]⟩ nothingPatch = .refuse 40 := by
  decide

theorem c4_abstract :
    ¬ ReleaseSafe nothingAuth ⟨[1]⟩ (releaseOf nothingPatch) [nothingPatch.trace] nothingPatch.sys :=
  empty_behaviors_refused nothingAuth 1 40 [nothingPatch.trace] nothingPatch.sys

def doorPatch (trace : List String) (sys : Bool → Bool) : Patch :=
  { basePatch 50 [0] trace with sys := sys, deps := [(1, 2)], symHigh := fun _ => true, obsHigh := fun _ => true, boundTime := 0, boundCompute := 0 }

theorem c5_check_order :
    check doorAuthority doorPrior (doorPatch ["stop", "open"] noiseSys) = .accept ∧
      check doorAuthority doorPrior (doorPatch ["open", "stop"] noiseSys) = .refuse 50 := by
  decide

theorem check_submitter_invariant :
    check doorAuthority doorPrior (doorPatch ["stop", "open"] noiseSys) =
      check doorAuthority doorPrior
        { doorPatch ["stop", "open"] noiseSys with deps := [(9, 9)], symHigh := fun _ => false, obsHigh := fun _ => true, boundTime := 1000, boundCompute := 1000 } := by
  decide

def appAuth : SpecAuthority where
  traceOK := fun _ => true
  eventOK := fun s b => s == 10 && b == 2
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10
  obsCost := fun _ => 1
  forbidden := []
  calls := [(11, 10)]
  roster := [10, 11]
  traceAllowed := fun _ => True
  eventAllowed := fun s b => s = 10 ∧ b = 2
  traceAgrees := by intro t; simp
  eventAgrees := by intro s b; simp [Bool.and_eq_true, beq_iff_eq]
  tracePrefixClosed := by intro t p _ _; trivial

def omittedPatch : Patch :=
  { basePatch 10 [2] ["stop"] with deps := [] }

def honestPatch : Patch :=
  { omittedPatch with deps := [(11, 10)] }

theorem c1_omitted_dep_refused :
    check appAuth ⟨[2]⟩ omittedPatch = .refuse 11 := by
  decide

theorem c1_deps_ignored :
    check appAuth ⟨[2]⟩ omittedPatch = check appAuth ⟨[2]⟩ honestPatch := by
  decide

def leakAuth : SpecAuthority where
  traceOK := fun _ => true
  eventOK := fun _ b => b == 7
  symHigh := fun _ => false
  obsHigh := fun b => b == 7
  boundTime := 10
  boundCompute := 10
  obsCost := fun _ => 1
  forbidden := []
  calls := []
  roster := [20]
  traceAllowed := fun _ => True
  eventAllowed := fun _ b => b = 7
  traceAgrees := by intro _; simp
  eventAgrees := by intro _ b; simp [beq_iff_eq]
  tracePrefixClosed := by intro _ _ _ _; trivial

def leakPatch : Patch := basePatch 20 [7] ["stop"]

def labeledPatch : Patch :=
  { leakPatch with obsHigh := fun b => b == 7, symHigh := fun _ => true }

theorem c2_unlabeled_leak_refused :
    check leakAuth ⟨[7]⟩ leakPatch = .refuse 20 := by
  decide

theorem c2_label_ignored :
    check leakAuth ⟨[7]⟩ leakPatch = check leakAuth ⟨[7]⟩ labeledPatch := by
  decide

def budgetAuth : SpecAuthority where
  traceOK := fun _ => true
  eventOK := fun _ b => b == 1 || b == 2 || b == 3 || b == 4
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 1
  boundCompute := 1
  obsCost := fun _ => 1
  forbidden := []
  calls := []
  roster := [30]
  traceAllowed := fun _ => True
  eventAllowed := fun _ b => b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4
  traceAgrees := by intro _; simp
  eventAgrees := by
    intro _ b
    simp [Bool.or_eq_true, beq_iff_eq, or_assoc]
  tracePrefixClosed := by intro _ _ _ _; trivial

def raisedPatch : Patch :=
  { basePatch 30 [1, 2, 3, 4] ["stop"] with boundTime := 1000, boundCompute := 1000 }

theorem c3_budget_raised_refused :
    check budgetAuth ⟨[1]⟩ raisedPatch = .refuse 30 := by
  decide

theorem changedCost_counts_obs :
    changedCost budgetAuth raisedPatch = 4 := by
  decide

theorem accept_cost_noWorse (spec : SpecAuthority) (prior : PriorQualification Nat) (p : Patch)
    (h : check spec prior p = .accept) :
    Optimality.noWorse (changedCost spec p, changedCost spec p)
      (spec.boundTime, spec.boundCompute) := by
  cases hadm : symbolAdmitted spec prior p with
  | false =>
    rw [check, hadm] at h
    nomatch h
  | true =>
    simp only [symbolAdmitted, Bool.and_eq_true] at hadm
    rcases hadm with ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hcost⟩
    simpa [Optimality.noWorse, Bool.and_eq_true, decide_eq_true_iff] using hcost

theorem incremental_release_safe (spec : SpecAuthority) (prior : PriorQualification Nat)
    (p : Patch) (h : check spec prior p = .accept) :
    ReleaseSafe spec prior (releaseOf p) [p.trace] p.sys ∧
      TaintFree spec.symHigh spec.obsHigh (releaseOf p) ∧
      Optimality.noWorse (changedCost spec p, changedCost spec p)
        (spec.boundTime, spec.boundCompute) :=
  ⟨(f4_checker_sound spec prior p h).1, (f4_checker_sound spec prior p h).2,
    accept_cost_noWorse spec prior p h⟩

theorem f4_instance :
    check doorAuthority doorPrior (doorPatch ["stop", "open"] noiseSys) = .accept ∧
      ReleaseSafe doorAuthority doorPrior
        (releaseOf (doorPatch ["stop", "open"] noiseSys)) [["stop", "open"]] noiseSys := by
  refine ⟨c5_check_order.1, ?_⟩
  exact (incremental_release_safe doorAuthority doorPrior
    (doorPatch ["stop", "open"] noiseSys) c5_check_order.1).1

#print axioms f4_checker_sound
#print axioms incremental_release_safe
#print axioms accept_cost_noWorse
#print axioms c1_omitted_dep_refused
#print axioms c2_unlabeled_leak_refused
#print axioms c3_budget_raised_refused
#print axioms c4_abstract
#print axioms c5_check_order
#print axioms check_submitter_invariant

end SoftwareIsIncrementallySafe
