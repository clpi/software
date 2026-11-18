import IncrementalCert.Check

namespace IncrementalCert

theorem omitted_refused :
    check specLeak prevLib omitDelta = Verdict.refuse "app" := by
  decide

theorem leak_unlabeled_refused :
    check specLabel prevLib { omitDelta with obsHigh := noObsHigh } = Verdict.refuse "app" := by
  decide

theorem budget_raised_refused :
    check specBudget prevNeed budgetDelta = Verdict.refuse "app" := by
  decide

theorem submitted_required_still_refused :
    check specBudget prevNeed { budgetDelta with
      changed := [("app", ["a"])]
      submittedRequired := [] } = Verdict.refuse "app" := by
  decide

structure ObsRelease (σ ω : Type) where
  behavior : σ → ω → Prop

def nothing {σ ω : Type} : ObsRelease σ ω where
  behavior _ _ := False

def HoldsRequired {σ ω : Type} (required : ω → Prop) (R : ObsRelease σ ω) : Prop :=
  ∀ o, required o → ∃ s, R.behavior s o

theorem nothing_refused {σ ω : Type} (required : ω → Prop) (h : ∃ o, required o) :
    ¬ HoldsRequired required (nothing (σ := σ) (ω := ω)) := by
  intro hR
  rcases h with ⟨o, ho⟩
  rcases hR o ho with ⟨_, hb⟩
  exact hb

end IncrementalCert
