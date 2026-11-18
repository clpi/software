import SoftwareIsIncrementallySafe.Checker
import SoftwareIsIncrementallySafe.Security

open SoftwareIsComposable

namespace SoftwareIsIncrementallySafe

def unitCost : String → Nat := fun _ => 1

def kindOf : String → NodeKind
  | "config" => .configuration
  | "ctx" => .context
  | "row" => .data
  | _ => .code

def appSpec : RepoSpec where
  symbols := ["app", "lib"]
  deps := [("app", "lib")]
  allow
    | "lib" => ["net"]
    | _ => []
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10
  required := fun _ => []
  obsCost := unitCost
  forbidden := []
  kind := kindOf

def omittedDelta : ExecDelta where
  changed := [("lib", ["net"])]
  deps := []
  inspect := ["lib"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10

def honestDelta : ExecDelta :=
  { omittedDelta with deps := [("app", "lib")], inspect := ["lib", "app"] }

theorem omitted_refused :
    check appSpec (fun _ => []) omittedDelta = Verdict.refuse "app" := by
  decide

theorem omitted_matches_honest :
    check appSpec (fun _ => []) omittedDelta =
      check appSpec (fun _ => []) honestDelta := by
  decide

def leakSpec : RepoSpec where
  symbols := ["handler"]
  deps := []
  allow := fun _ => ["secret_out"]
  symHigh := fun _ => false
  obsHigh := fun o => o == "secret_out"
  boundTime := 10
  boundCompute := 10
  required := fun _ => []
  obsCost := unitCost
  forbidden := []
  kind := kindOf

def leakUnlabeledDelta : ExecDelta where
  changed := [("handler", ["secret_out"])]
  deps := []
  inspect := ["handler"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10

def leakLabeledDelta : ExecDelta :=
  { leakUnlabeledDelta with obsHigh := fun o => o == "secret_out" }

theorem leak_unlabeled_refused :
    check leakSpec (fun _ => []) leakUnlabeledDelta = Verdict.refuse "handler" := by
  decide

theorem leak_label_ignored :
    check leakSpec (fun _ => []) leakUnlabeledDelta =
      check leakSpec (fun _ => []) leakLabeledDelta := by
  decide

def budgetSpec : RepoSpec where
  symbols := ["lib"]
  deps := []
  allow := fun _ => ["a", "b", "c", "d"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 1
  boundCompute := 1
  required := fun _ => []
  obsCost := unitCost
  forbidden := []
  kind := kindOf

def raisedDelta : ExecDelta where
  changed := [("lib", ["a", "b", "c", "d"])]
  deps := []
  inspect := ["lib"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 1000
  boundCompute := 1000

def tightDelta : ExecDelta :=
  { raisedDelta with boundTime := 1, boundCompute := 1 }

theorem budget_raised_refused :
    check budgetSpec (fun _ => []) raisedDelta = Verdict.refuse "lib" := by
  decide

theorem budget_field_ignored :
    check budgetSpec (fun _ => []) raisedDelta =
      check budgetSpec (fun _ => []) tightDelta := by
  decide

def liveSpec : RepoSpec where
  symbols := ["lib"]
  deps := []
  allow := fun _ => ["serve", "idle"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10
  required := fun s => if s == "lib" then ["serve"] else []
  obsCost := unitCost
  forbidden := []
  kind := kindOf

def emptyDelta : ExecDelta where
  changed := [("lib", [])]
  deps := []
  inspect := []
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 1000
  boundCompute := 1000

def dropServe : ExecDelta :=
  { emptyDelta with changed := [("lib", ["idle"])] }

theorem empty_patch_refused :
    check liveSpec (fun _ => []) emptyDelta = Verdict.refuse "lib" := by
  decide

theorem dropped_required_refused :
    check liveSpec (fun _ => []) dropServe = Verdict.refuse "lib" := by
  decide

theorem required_survives_submitter :
    check liveSpec (fun _ => []) emptyDelta =
      check liveSpec (fun _ => [])
        { emptyDelta with deps := [("lib", "lib")], inspect := [], boundTime := 0, boundCompute := 0 } := by
  decide

def emptyRelease {σ ω : Type} : Release σ ω :=
  ⟨fun _ => ⟨fun _ => False⟩⟩

def specRequired {σ ω : Type} (prev : Release σ ω) (s : σ) : ω → Prop :=
  (prev.behavior s).obs

theorem nothing_refused {σ ω : Type} (prev : Release σ ω) (allowed : σ → ω → Prop)
    (hprev : ∃ s o, specRequired prev s o) :
    ¬ ((∀ s o, specRequired prev s o → (emptyRelease.behavior s).obs o) ∧
       (∀ s o, (emptyRelease.behavior s).obs o → allowed s o)) := by
  intro h
  rcases hprev with ⟨s, o, ho⟩
  exact h.1 s o ho

def doorStopped : List String → Bool
  | [] => true
  | _ :: rest => doorStopped rest

def door : List String → Bool
  | [] => true
  | "stop" :: rest => doorStopped rest
  | "open" :: _ => false
  | _ :: rest => door rest

theorem order_distinguished :
    door ["stop", "open"] = true ∧ door ["open", "stop"] = false := by
  decide

theorem allow_list_ignores_order {ω : Type} (A : ω → Prop) (a b : ω) :
    allowedTrace A [a, b] ↔ allowedTrace A [b, a] := by
  constructor <;> intro h o ho <;> apply h <;> simp at ho ⊢ <;> exact ho.symm

def profileOf (f : Bool → Bool → Prop) : Profile Bool :=
  ⟨fun o => ∃ s, f s o⟩

def leakBit : Bool → Bool → Prop := fun s o => o = s

def noiseBit : Bool → Bool → Prop := fun _ _ => True

theorem same_profile : profileOf leakBit = profileOf noiseBit := by
  unfold profileOf leakBit noiseBit
  congr 1
  funext o
  apply propext
  exact ⟨fun _ => ⟨o, trivial⟩, fun _ => ⟨o, rfl⟩⟩

def gm (sys : Bool → Bool) : Prop :=
  ∀ h1 h2, sys h1 = sys h2

def leakSys : Bool → Bool := fun s => s

def noiseSys : Bool → Bool := fun _ => false

theorem leak_not_gm : ¬ gm leakSys := by
  intro h
  have := h true false
  simp [gm, leakSys] at this

theorem noise_gm : gm noiseSys :=
  fun _ _ => rfl

theorem config_change_includes_worker :
    "worker" ∈ coneExecOf [("worker", "config")] ["config"] := by
  decide

theorem config_is_configuration : kindOf "config" = NodeKind.configuration := rfl

theorem context_is_context : kindOf "ctx" = NodeKind.context := rfl

theorem data_is_data : kindOf "row" = NodeKind.data := rfl

theorem behaviorAfter_fun (base : String → List String) (d1 d2 : ExecDelta)
    (h : d1.changed = d2.changed) :
    behaviorAfter base d1 = behaviorAfter base d2 := by
  funext s
  simp [behaviorAfter, h]

theorem check_submitter_invariant (spec : RepoSpec) (base : String → List String)
    (d1 d2 : ExecDelta) (h : d1.changed = d2.changed) :
    check spec base d1 = check spec base d2 := by
  cases d1
  cases d2
  cases h
  rfl

#print axioms omitted_refused
#print axioms leak_unlabeled_refused
#print axioms budget_raised_refused
#print axioms nothing_refused
#print axioms order_distinguished
#print axioms same_profile
#print axioms leak_not_gm
#print axioms noise_gm
#print axioms check_submitter_invariant

end SoftwareIsIncrementallySafe
