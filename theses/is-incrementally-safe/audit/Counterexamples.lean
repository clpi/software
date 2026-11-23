/-
  Independent counterexamples for clpi/software-is-incrementally-safe
  (branch cursor/incremental-safety-0f5e @ de1b30716e2b), which also carries
  the SoftwareIsComposable and SoftwareIsIncrementallyCertifiable modules.
  Build: from that repo, `lake env lean <this file>`.
  Each item is a kernel-checked fact about the repo's own definitions.
-/
import SoftwareIsIncrementallySafe

open SoftwareIsComposable SoftwareIsIncrementallyCertifiable SoftwareIsIncrementallySafe

namespace AuditCounterexamples

/-! ## C1. The executable checker trusts the submitter's dependency list.
`app` depends on `lib`. The change makes `lib` emit "net", which `app` is not
allowed to observe. With the true dependency edge the checker refuses `app`.
With the edge omitted from the delta (the delta carries its own `deps`), the
same behavioral change is accepted. -/
def allow : String → List String
  | "lib" => ["net"]
  | _ => []

def honest : ExecDelta where
  changed := [("lib", ["net"])]
  deps := [("app", "lib")]
  inspect := ["lib", "app"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10

def omitted : ExecDelta := { honest with deps := [], inspect := ["lib"] }

theorem honest_refused : check [] allow (fun _ => []) honest = .refuse "app" := by decide
theorem omitted_accepted : check [] allow (fun _ => []) omitted = .accept := by decide

/-! ## C2. The submitter also declares which observations are secret.
A low symbol reaching "secret_out" is refused when the delta marks it high,
and accepted when the same delta marks nothing high. -/
def leakHonest : ExecDelta where
  changed := [("handler", ["secret_out"])]
  deps := []
  inspect := ["handler"]
  symHigh := fun _ => false
  obsHigh := fun o => o == "secret_out"
  boundTime := 10
  boundCompute := 10

def leakUnlabeled : ExecDelta := { leakHonest with obsHigh := fun _ => false }

def allowAll : String → List String := fun _ => ["secret_out"]

theorem leak_refused : check [] allowAll (fun _ => []) leakHonest = .refuse "handler" := by decide
theorem leak_accepted : check [] allowAll (fun _ => []) leakUnlabeled = .accept := by decide

/-! ## C3. The cost budget is also part of the submitted delta. -/
def bigChange : ExecDelta where
  changed := [("lib", ["a", "b", "c", "d"])]
  deps := []
  inspect := ["lib"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 1
  boundCompute := 1

theorem over_budget_refused :
    check [] (fun _ => ["a", "b", "c", "d"]) (fun _ => []) bigChange = .refuse "lib" := by decide
theorem budget_raised_accepted :
    check [] (fun _ => ["a", "b", "c", "d"]) (fun _ => [])
      { bigChange with boundTime := 1000, boundCompute := 1000 } = .accept := by decide

/-! ## C4. A release that does nothing is maximally "safe" and "monotone".
Deleting every behavior satisfies every allow-list, every NI condition and
the monotonicity premise. Safety in this model never requires liveness. -/
def nothing {σ ω : Type} : Release σ ω := ⟨fun _ => ⟨fun _ => False⟩⟩

theorem nothing_safe {σ ω : Type} (allow : σ → ω → Prop) (deps : σ → σ → Prop) :
    ReleaseSafe allow deps (nothing (σ := σ) (ω := ω)) := by
  intro s o h
  exfalso
  induction h with
  | here hobs => exact hobs
  | step _ _ ih => exact ih

theorem nothing_below {σ ω : Type} (R : Release σ ω) : releaseLE nothing R :=
  fun _ _ h => h.elim

/-! ## C5. "Traces" here are unordered. Any allow-list trace property gives the
same verdict to [open, stop] and [stop, open], so an ordering requirement such
as "never open the door before the train stops" is not expressible as
`allowedTrace A`. The safety theorems are therefore about per-event allow-lists,
not about safety properties over sequences in the Alpern–Schneider sense. -/
theorem allowedTrace_swap {ω : Type} (A : ω → Prop) (a b : ω) :
    allowedTrace A [a, b] ↔ allowedTrace A [b, a] := by
  constructor <;> intro h o ho <;> apply h <;> simp at ho ⊢ <;> exact ho.symm

/-! ## C6. A set-of-observations profile cannot see information flow.
`leak` outputs the secret bit; `noise` outputs either bit regardless of the
secret. They induce the same profile, so any check defined on profiles
(including the repo's `NI`) gives them the same verdict, although only `leak`
reveals the secret. Noninterference in the Goguen–Meseguer sense relates pairs
of runs and is not a property of this set. -/
def profileOf (f : Bool → Bool → Prop) : Profile Bool := ⟨fun o => ∃ s, f s o⟩
def leak : Bool → Bool → Prop := fun s o => o = s
def noise : Bool → Bool → Prop := fun _ _ => True

theorem same_profile : profileOf leak = profileOf noise := by
  unfold profileOf leak noise
  congr 1
  funext o
  apply propext
  exact ⟨fun _ => ⟨o, trivial⟩, fun _ => ⟨o, rfl⟩⟩

theorem leak_reveals : ∀ s o, leak s o → o = s := fun _ _ h => h
theorem noise_hides : ∀ s o, noise s o := fun _ _ => trivial

end AuditCounterexamples

#print axioms AuditCounterexamples.omitted_accepted
#print axioms AuditCounterexamples.leak_accepted
#print axioms AuditCounterexamples.budget_raised_accepted
#print axioms AuditCounterexamples.nothing_safe
#print axioms AuditCounterexamples.allowedTrace_swap
#print axioms AuditCounterexamples.same_profile
