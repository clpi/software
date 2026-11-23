import CanonicalDominance

namespace IncrementalCert

inductive Verdict where
  | accept
  | refuse (symbol : String)
  deriving DecidableEq, Repr

structure Spec where
  symbols : List String
  deps : List (String × String)
  symHigh : String → Bool
  obsHigh : String → Bool
  allow : String → List String
  boundTime : Nat
  boundCompute : Nat
  required : List String
  allowed : List String
  forb : List String

structure Prev where
  base : String → List String
  qualified : List String

structure Delta where
  changed : List (String × List String)
  deps : List (String × String)
  inspect : List String
  symHigh : String → Bool
  obsHigh : String → Bool
  boundTime : Nat
  boundCompute : Nat
  submittedRequired : List String
  submittedAllowed : List String

structure Certificate where
  spec : Spec
  prev : Prev

def priorOf (prev : Prev) : SoftwareIsQuantifiable.Pareto.PriorQualification String where
  qualified := prev.qualified

def requiredOf (prev : Prev) : List String :=
  (priorOf prev).qualified

def allowedOf (spec : Spec) : List String :=
  spec.allowed

structure RequiredNonempty (prev : Prev) : Prop where
  nonempty : requiredOf prev ≠ []

theorem required_is_prior (prev : Prev) :
    requiredOf prev = (priorOf prev).qualified := rfl

theorem allowed_is_spec (spec : Spec) :
    allowedOf spec = spec.allowed := rfl

def behaviorAfter (base : String → List String)
    (changed : List (String × List String)) (s : String) : List String :=
  match changed.find? (fun p => p.fst == s) with
  | some p => p.snd
  | none => base s

def directDeps (deps : List (String × String)) (s : String) : List String :=
  (deps.filter (fun e => e.fst == s)).map Prod.snd

def pushNew (seen queue : List String) (t : String) : List String × List String :=
  if seen.contains t then (seen, queue) else (t :: seen, queue ++ [t])

def pushAll (seen queue : List String) : List String → List String × List String
  | [] => (seen, queue)
  | t :: ts =>
    let step := pushNew seen queue t
    pushAll step.1 step.2 ts

def visit (deps : List (String × String)) (beh : String → List String) :
    Nat → List String → List String → List String → List String
  | 0, _, _, acc => acc
  | _, _, [], acc => acc
  | n + 1, seen, s :: rest, acc =>
    let step := pushAll (s :: seen) rest (directDeps deps s)
    visit deps beh n step.1 step.2 (acc ++ beh s)

def reachedObs (deps : List (String × String)) (beh : String → List String)
    (s : String) : List String :=
  visit deps beh (2 * deps.length + 2) [s] [s] []

theorem cycle_obs_once :
    (reachedObs [("a", "b"), ("b", "a")] (fun _ => ["x"]) "a").length = 2 := by
  decide

def isUnsafe (spec : Spec) (beh : String → List String) (s : String) : Bool :=
  let got := reachedObs spec.deps beh s
  got.any (fun o => !(spec.allow s).contains o) ||
    (!spec.symHigh s && got.any spec.obsHigh) ||
    (spec.forb.contains s && !(beh s).isEmpty)

def changedCost (changed : List (String × List String)) : Nat :=
  changed.foldl (fun n p => n + p.snd.length) 0

def collected (spec : Spec) (base : String → List String)
    (changed : List (String × List String)) : List String :=
  spec.symbols.flatMap (behaviorAfter base changed)

def accepted (spec : Spec) (prev : Prev)
    (changed : List (String × List String)) : Bool :=
  let req := requiredOf prev
  let allw := allowedOf spec
  let beh := behaviorAfter prev.base changed
  let got := collected spec prev.base changed
  let cost := changedCost changed
  !req.isEmpty &&
    req.all (fun b => got.contains b) &&
    got.all (fun b => allw.contains b) &&
    spec.symbols.all (fun s => !isUnsafe spec beh s) &&
    decide (cost ≤ spec.boundTime) &&
    decide (cost ≤ spec.boundCompute)

def blame (spec : Spec) (prev : Prev)
    (changed : List (String × List String)) : String :=
  let beh := behaviorAfter prev.base changed
  match spec.symbols.find? (fun s => isUnsafe spec beh s) with
  | some s => s
  | none =>
    match changed with
    | p :: _ => p.fst
    | [] => "release"

def check (spec : Spec) (prev : Prev) (d : Delta) : Verdict :=
  if accepted spec prev d.changed then .accept else .refuse (blame spec prev d.changed)

def nextPrev (spec : Spec) (prev : Prev) (changed : List (String × List String)) : Prev where
  base := behaviorAfter prev.base changed
  qualified := collected spec prev.base changed

def cert (c : Certificate) (d : Delta) : Option Certificate :=
  if accepted c.spec c.prev d.changed then
    some { c with prev := nextPrev c.spec c.prev d.changed }
  else
    none

theorem check_ignores_spec_required (spec : Spec) (prev : Prev) (d : Delta)
    (req : List String) :
    check { spec with required := req } prev d = check spec prev d := rfl

theorem check_submitter_invariant (spec : Spec) (prev : Prev) (d1 d2 : Delta)
    (h : d1.changed = d2.changed) :
    check spec prev d1 = check spec prev d2 := by
  simp [check, h]

def ReleasePred (spec : Spec) (prev : Prev)
    (changed : List (String × List String)) : Prop :=
  let req := requiredOf prev
  let allw := allowedOf spec
  let got := collected spec prev.base changed
  let beh := behaviorAfter prev.base changed
  req ≠ [] ∧
    (∀ b, b ∈ req → b ∈ got) ∧
    (∀ b, b ∈ got → b ∈ allw) ∧
    (∀ s, s ∈ spec.symbols → isUnsafe spec beh s = false) ∧
    changedCost changed ≤ spec.boundTime ∧
    changedCost changed ≤ spec.boundCompute

theorem not_isEmpty_ne {α : Type} (l : List α) : (!l.isEmpty) = true ↔ l ≠ [] := by
  cases l <;> simp [List.isEmpty]

theorem check_accept_iff (spec : Spec) (prev : Prev) (d : Delta) :
    check spec prev d = Verdict.accept ↔ accepted spec prev d.changed = true := by
  cases h : accepted spec prev d.changed <;> simp [check, h]

theorem accepted_sound (spec : Spec) (prev : Prev)
    (changed : List (String × List String))
    (h : accepted spec prev changed = true) :
    ReleasePred spec prev changed := by
  simp [accepted, Bool.and_eq_true, List.all_eq_true, List.contains_iff,
    decide_eq_true_iff, not_isEmpty_ne] at h
  rcases h with ⟨⟨⟨⟨⟨hne, hreq⟩, hall⟩, hunsafe⟩, htime⟩, hcomp⟩
  exact ⟨hne, hreq, hall, hunsafe, htime, hcomp⟩

theorem check_sound (spec : Spec) (prev : Prev) (d : Delta)
    (h : check spec prev d = Verdict.accept) :
    ReleasePred spec prev d.changed :=
  accepted_sound spec prev d.changed ((check_accept_iff spec prev d).mp h)

def lowSym (_ : String) : Bool := false

def noObsHigh (_ : String) : Bool := false

def secretHigh (o : String) : Bool := o == "secret"

def allowApp : String → List String
  | "app" => ["need", "ok"]
  | _ => ["need", "ok", "secret"]

def allowLeak : String → List String
  | _ => ["need", "ok", "secret"]

def allowBudget : String → List String
  | _ => ["need", "a", "b", "c"]

def baseLib : String → List String
  | "lib" => ["secret"]
  | "app" => ["need"]
  | _ => []

def baseNeed : String → List String
  | "app" => ["need"]
  | _ => []

def specLeak : Spec where
  symbols := ["app", "lib"]
  deps := [("app", "lib")]
  symHigh := lowSym
  obsHigh := secretHigh
  allow := allowApp
  boundTime := 4
  boundCompute := 4
  required := ["need"]
  allowed := ["need", "ok", "secret"]
  forb := []

def specLabel : Spec :=
  { specLeak with allow := allowLeak }

def specBudget : Spec where
  symbols := ["app"]
  deps := []
  symHigh := lowSym
  obsHigh := noObsHigh
  allow := allowBudget
  boundTime := 1
  boundCompute := 1
  required := ["need"]
  allowed := ["need", "a", "b", "c"]
  forb := []

def prevLib : Prev where
  base := baseLib
  qualified := ["need"]

def prevNeed : Prev where
  base := baseNeed
  qualified := ["need"]

def omitDelta : Delta where
  changed := [("app", ["need"])]
  deps := []
  inspect := []
  symHigh := lowSym
  obsHigh := noObsHigh
  boundTime := 100
  boundCompute := 100
  submittedRequired := []
  submittedAllowed := []

def leakDelta : Delta :=
  { omitDelta with deps := [("app", "lib")], obsHigh := secretHigh }

def budgetDelta : Delta where
  changed := [("app", ["need", "a", "b", "c"])]
  deps := []
  inspect := ["app"]
  symHigh := lowSym
  obsHigh := noObsHigh
  boundTime := 100
  boundCompute := 100
  submittedRequired := ["need"]
  submittedAllowed := ["need", "a", "b", "c"]

def behaviorMap (base : String → List String)
    (changed : List (String × List String)) : String → List String :=
  behaviorAfter base changed

theorem empty_behaviors_refused :
    accepted specBudget prevNeed [("app", [])] = false := by
  decide

theorem spec_required_empty_still_refused :
    check { specBudget with required := [] } prevNeed
      { budgetDelta with changed := [("app", [])], submittedRequired := [] } =
        Verdict.refuse "app" := by
  decide

theorem incremental_eq_scratch :
    behaviorAfter (behaviorMap baseNeed [("lib", ["x"])]) [("app", ["need"])] "app" =
      behaviorAfter baseNeed ([("lib", ["x"]), ("app", ["need"])]) "app" ∧
    behaviorAfter (behaviorMap baseNeed [("lib", ["x"])]) [("app", ["need"])] "lib" =
      behaviorAfter baseNeed ([("lib", ["x"]), ("app", ["need"])]) "lib" := by
  decide

end IncrementalCert
