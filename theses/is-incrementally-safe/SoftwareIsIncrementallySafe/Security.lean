import SoftwareIsIncrementallySafe.Increment

namespace SoftwareIsIncrementallySafe

open SoftwareIsComposable
open SoftwareIsIncrementallyCertifiable
open Classical

theorem capability_within_allowance {σ ω : Type}
    (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    (R : Release σ ω) (d : Delta σ ω)
    (hR : ReleaseSafe allow deps R)
    (hClo : ClosureHyp deps d)
    (hAcc : ConeAccept allow deps R d) :
    Within allow deps (apply R d).behavior :=
  preserve_safety allow deps R d hR hClo hAcc

theorem chain_capabilities_within_allowance {σ ω : Type}
    (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    {c : Chain σ ω}
    (hClo : Chain.closureHyps deps c)
    (h : Chain.incrAccept allow deps c) :
    Within allow deps c.final.behavior :=
  chain_final_of_incremental allow deps hClo h

theorem capability_shrinks {σ ω : Type}
    (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    (R : Release σ ω) (d : Delta σ ω)
    (hmono : ∀ s, d.changed s = true → profileLE (d.update s) (R.behavior s))
    (hR : Within allow deps R.behavior) :
    Within allow deps (apply R d).behavior := by
  intro s o hr
  exact hR s o (reaches_monotone (fun s => incremental_monotone R d hmono s) hr)

def TaintFree {σ ω : Type} (deps : σ → σ → Prop) (symHigh : σ → Bool) (obsHigh : ω → Bool)
    (B : σ → Profile ω) : Prop :=
  ∀ s o, Reaches deps B s o → symHigh s = false → obsHigh o = false

def TaintAccept {σ ω : Type} (deps : σ → σ → Prop) (symHigh : σ → Bool) (obsHigh : ω → Bool)
    (R : Release σ ω) (d : Delta σ ω) : Prop :=
  ∀ s, d.inspect s = true →
    ∀ o, Reaches deps (apply R d).behavior s o → symHigh s = false → obsHigh o = false

theorem taintfree_preserved {σ ω : Type}
    (deps : σ → σ → Prop) (symHigh : σ → Bool) (obsHigh : ω → Bool)
    (R : Release σ ω) (d : Delta σ ω)
    (hR : TaintFree deps symHigh obsHigh R.behavior)
    (hClo : ClosureHyp deps d)
    (hAcc : TaintAccept deps symHigh obsHigh R d) :
    TaintFree deps symHigh obsHigh (apply R d).behavior := by
  intro s o hr hlow
  by_cases hc : Cone deps d.changed s
  · exact hAcc s (hClo s hc) o hr hlow
  · exact hR s o ((reaches_outside_stable (fun t ht => apply_unchanged R d ht) hc).mp hr) hlow

def Chain.taintAccept {σ ω : Type} (deps : σ → σ → Prop) (symHigh : σ → Bool)
    (obsHigh : ω → Bool) : Chain σ ω → Prop
  | .base R => TaintFree deps symHigh obsHigh R.behavior
  | .step prev d =>
      prev.taintAccept deps symHigh obsHigh ∧ ClosureHyp deps d ∧
        TaintAccept deps symHigh obsHigh prev.final d

theorem chain_taintfree {σ ω : Type}
    (deps : σ → σ → Prop) (symHigh : σ → Bool) (obsHigh : ω → Bool)
    (c : Chain σ ω) :
    Chain.taintAccept deps symHigh obsHigh c →
      TaintFree deps symHigh obsHigh c.final.behavior := by
  induction c with
  | base _ =>
    intro h
    exact h
  | step prev d ih =>
    intro h
    rcases h with ⟨hprev, hClo, hAcc⟩
    exact taintfree_preserved deps symHigh obsHigh prev.final d (ih hprev) hClo hAcc

def ForbiddenSafe {σ ω : Type} (forb : σ → Prop) (R : Release σ ω) : Prop :=
  ∀ s, forb s → ∀ o, ¬ (R.behavior s).obs o

def ForbiddenAccept {σ ω : Type} (forb : σ → Prop) (R : Release σ ω) (d : Delta σ ω) : Prop :=
  ∀ s, d.inspect s = true → forb s → ∀ o, ¬ ((apply R d).behavior s).obs o

theorem forbidden_preserved {σ ω : Type}
    (forb : σ → Prop) (deps : σ → σ → Prop)
    (R : Release σ ω) (d : Delta σ ω)
    (hR : ForbiddenSafe forb R)
    (hClo : ClosureHyp deps d)
    (hAcc : ForbiddenAccept forb R d) :
    ForbiddenSafe forb (apply R d) := by
  intro s hs o ho
  by_cases hc : Cone deps d.changed s
  · exact hAcc s (hClo s hc) hs o ho
  · rw [apply_unchanged R d (not_cone_not_changed hc)] at ho
    exact hR s hs o ho

def ForbMeansEmpty {σ ω : Type} (forb : σ → Prop) (allow : σ → ω → Prop) : Prop :=
  ∀ s, forb s → ∀ o, ¬ allow s o

theorem forbidden_introduced_refused {σ ω : Type}
    (forb : σ → Prop) (allow : σ → ω → Prop) (deps : σ → σ → Prop)
    (R : Release σ ω) (d : Delta σ ω) {s : σ} {o : ω}
    (hpol : ForbMeansEmpty forb allow)
    (hf : forb s)
    (hchg : d.changed s = true)
    (ho : (d.update s).obs o)
    (hClo : ClosureHyp deps d) :
    ¬ ConeAccept allow deps R d := by
  intro hAcc
  have hr : Reaches deps (apply R d).behavior s o :=
    Reaches.here (by
      rw [apply_changed R d hchg]
      exact ho)
  exact hpol s hf o (hAcc s (hClo s (cone_of_changed hchg)) o hr)

theorem authority_pareto_bounded {used bound allowance : Cost}
    (hUsed : paretoLE used bound) (hBound : paretoLE bound allowance) :
    paretoLE used allowance :=
  paretoLE_trans hUsed hBound

theorem admitted_release_downward {ω : Type}
    {safe : Profile ω → Prop} {bound : Cost} {a b : Admission ω}
    (hA : admits safe bound a)
    (hp : profileLE b.profile a.profile)
    (hc : paretoLE b.cost a.cost) :
    admits safe bound b :=
  admitted_downward hA hp hc

end SoftwareIsIncrementallySafe
