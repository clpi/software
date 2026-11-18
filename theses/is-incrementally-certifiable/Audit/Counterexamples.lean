namespace Audit.Counterexamples

inductive Verdict where
  | accept
  | refuse (symbol : String)
  deriving DecidableEq, Repr

structure OldDelta where
  changed : List (String × List String)
  deps : List (String × String)
  inspect : List String
  symHigh : String → Bool
  obsHigh : String → Bool
  boundTime : Nat
  boundCompute : Nat

def changedSymbols (d : OldDelta) : List String :=
  d.changed.map Prod.fst

def behaviorAfter (base : String → List String) (d : OldDelta) (s : String) : List String :=
  match d.changed.find? (fun p => p.fst == s) with
  | some p => p.snd
  | none => base s

def directDeps (deps : List (String × String)) (s : String) : List String :=
  (deps.filter (fun e => e.fst == s)).map Prod.snd

def reachable (deps : List (String × String)) (beh : String → List String)
    (s : String) : Nat → List String
  | 0 => []
  | n + 1 =>
    beh s ++ List.flatMap (fun t => reachable deps beh t n) (directDeps deps s)

def reachedObs (deps : List (String × String)) (beh : String → List String)
    (s : String) : List String :=
  reachable deps beh s (deps.length + 1)

def parentsOf : List (String × String) → List String → List String
  | [], _ => []
  | e :: es, acc =>
    if acc.contains e.snd then e.fst :: parentsOf es acc else parentsOf es acc

def expand (deps : List (String × String)) (acc : List String) : List String :=
  acc ++ (parentsOf deps acc).filter (fun s => !acc.contains s)

def iterCone (deps : List (String × String)) (acc : List String) : Nat → List String
  | 0 => acc
  | n + 1 => expand deps (iterCone deps acc n)

def coneExec (d : OldDelta) : List String :=
  iterCone d.deps (changedSymbols d) (d.deps.length + (changedSymbols d).length + 1)

def isUnsafeObs (allow : String → List String) (beh : String → List String)
    (symHigh obsHigh : String → Bool) (deps : List (String × String)) (s : String) : Bool :=
  let got := reachedObs deps beh s
  got.any (fun o => !(allow s).contains o) || (!symHigh s && got.any obsHigh)

def changedCost (d : OldDelta) : Nat :=
  d.changed.foldl (fun n p => n + p.snd.length) 0

def paretoOK (d : OldDelta) : Bool :=
  decide (changedCost d ≤ d.boundTime) && decide (changedCost d ≤ d.boundCompute)

def check (allow base : String → List String) (d : OldDelta) : Verdict :=
  match (coneExec d).find? (fun s => !d.inspect.contains s) with
  | some s => .refuse s
  | none =>
    match (coneExec d).find? (fun s =>
        isUnsafeObs allow (behaviorAfter base d) d.symHigh d.obsHigh d.deps s) with
    | some s => .refuse s
    | none =>
      if paretoOK d then .accept
      else
        match changedSymbols d with
        | s :: _ => .refuse s
        | [] => .accept

def low (_ : String) : Bool := false

def allowOk : String → List String
  | "app" => ["ok"]
  | _ => ["ok", "secret"]

def baseBeh : String → List String
  | "lib" => ["secret"]
  | _ => []

def edge : List (String × String) := [("app", "lib")]

def c1 (deps : List (String × String)) : OldDelta where
  changed := [("app", [])]
  deps := deps
  inspect := ["app", "lib"]
  symHigh := low
  obsHigh := fun o => o == "secret"
  boundTime := 4
  boundCompute := 4

theorem c1_true_edge_refuses :
    check allowOk baseBeh (c1 edge) = Verdict.refuse "app" := by
  decide

theorem c1_omitted_edge_accepts :
    check allowOk baseBeh (c1 []) = Verdict.accept := by
  decide

def allowAll : String → List String
  | _ => ["ok", "secret"]

def c2 (label : String → Bool) : OldDelta where
  changed := [("app", [])]
  deps := edge
  inspect := ["app", "lib"]
  symHigh := low
  obsHigh := label
  boundTime := 4
  boundCompute := 4

theorem c2_label_refuses_leak :
    check allowAll baseBeh (c2 (fun o => o == "secret")) = Verdict.refuse "app" := by
  decide

theorem c2_label_hides_leak :
    check allowAll baseBeh (c2 (fun _ => false)) = Verdict.accept := by
  decide

def c3 (bound : Nat) : OldDelta where
  changed := [("app", ["a", "b", "c"])]
  deps := []
  inspect := ["app"]
  symHigh := low
  obsHigh := fun _ => false
  boundTime := bound
  boundCompute := bound

def allowLetters : String → List String
  | _ => ["a", "b", "c"]

def baseEmpty : String → List String
  | _ => []

theorem c3_tight_budget_refuses :
    check allowLetters baseEmpty (c3 1) = Verdict.refuse "app" := by
  decide

theorem c3_raised_budget_accepts :
    check allowLetters baseEmpty (c3 10) = Verdict.accept := by
  decide

structure Profile (ω : Type) where
  obs : ω → Prop

structure Release (σ ω : Type) where
  behavior : σ → Profile ω

def nothing {σ ω : Type} : Release σ ω where
  behavior _ := ⟨fun _ => False⟩

def releaseLE {σ ω : Type} (R S : Release σ ω) : Prop :=
  ∀ s o, (R.behavior s).obs o → (S.behavior s).obs o

inductive Reaches {σ ω : Type} (deps : σ → σ → Prop) (B : σ → Profile ω) : σ → ω → Prop where
  | here {s : σ} {o : ω} : (B s).obs o → Reaches deps B s o
  | step {s t : σ} {o : ω} : deps s t → Reaches deps B t o → Reaches deps B s o

def NI {σ ω : Type} (deps : σ → σ → Prop) (symHigh : σ → Bool) (obsHigh : ω → Bool)
    (B : σ → Profile ω) : Prop :=
  ∀ s o, Reaches deps B s o → symHigh s = false → obsHigh o = false

def Safe {σ ω : Type} (allow : ω → Prop) (R : Release σ ω) : Prop :=
  ∀ s o, (R.behavior s).obs o → allow o

theorem reaches_nothing {σ ω : Type} (deps : σ → σ → Prop) (s : σ) (o : ω) :
    ¬ Reaches deps (nothing (σ := σ) (ω := ω)).behavior s o := by
  intro h
  induction h with
  | here hobs => exact hobs
  | step _ _ ih => exact ih

theorem c4_nothing_safe {σ ω : Type} (allow : ω → Prop) :
    Safe allow (nothing (σ := σ) (ω := ω)) := by
  intro _ _ h
  exact False.elim h

theorem c4_nothing_ni {σ ω : Type} (deps : σ → σ → Prop) (symHigh : σ → Bool)
    (obsHigh : ω → Bool) :
    NI deps symHigh obsHigh (nothing (σ := σ) (ω := ω)).behavior := by
  intro s o hr _
  exact False.elim (reaches_nothing deps s o hr)

theorem c4_releaseLE_nothing {σ ω : Type} (R : Release σ ω) :
    releaseLE (nothing (σ := σ) (ω := ω)) R := by
  intro _ _ h
  exact False.elim h

end Audit.Counterexamples
