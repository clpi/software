import SoftwareIsIncrementallySafe.OrderedIncrement

/-!
# How little can a release recheck?

`recheck_iff_scratch` (software-is-incrementally-safe) says rechecking the dependency cone of a
change is as good as rechecking everything, given the `Local` premise. This module answers the
two questions that theorem leaves open.

1. Can a rule that sees only the dependency graph and the changed set recheck less than the
   cone? No. `cone_least` shows any such rule that is sound for every local semantics and every
   per-symbol property must recheck every cone member. With `recheck_iff_scratch` this makes
   the cone the least sound graph-only selection.
2. When can a release recheck less than the cone? `refining_change_sound` shows that when the
   property is subset-closed, the semantics is monotone in component behavior, and each changed
   component refines its old behavior (a check on the changed components only), nothing else
   needs rechecking. `not_monotone_breaks` and the upstream `naive_changed_only_false` show the
   monotonicity and subset-closure premises each carry weight: drop either and a changed-only
   check accepts a bad release.

Prior art. Safe regression test selection and its precision (Rothermel and Harrold 1996, 1997),
minimal incremental builds (Mokhov, Mitchell and Peyton Jones 2018), preservation of
subset-closed hyperproperties under refinement (Clarkson and Schneider 2010), and the
refinement paradox for noninterference (McLean 1994; Jacob 1989). `cone_least` is the folklore
adversary argument behind "safe selection needs the transitive closure"; we know of no earlier
mechanized statement of it, but the result itself is not new. The two-way selection rule is a
packaging of these known facts as one release-gate decision, not a new theorem.
-/
namespace Family.Selection

open SoftwareIsIncrementallySafe.OrderedIncrement

/-- The cone in its plain form: `s` reaches a changed symbol along dependencies. -/
def Reach {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) (s : σ) : Prop :=
  ∃ u, DepStar deps s u ∧ changed u = true

abbrev Cone {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) (s : σ) : Prop :=
  HypergraphIncremental.Affected (depGraph deps fun _ => False)
    (depGraph deps fun x => changed x = true) s

theorem reach_cone {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool} {s : σ}
    (h : Reach deps changed s) : Cone deps changed s := by
  obtain ⟨u, hsu, hu⟩ := h
  induction hsu with
  | refl _ => exact affected_root hu
  | step hd _ ih => exact affected_step hd (ih hu)

theorem cone_reach {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool} {s : σ}
    (h : Cone deps changed s) : Reach deps changed s := by
  induction h with
  | root hr =>
    rename_i a
    refine ⟨a, .refl a, ?_⟩
    cases hc : changed a with
    | true => rfl
    | false => exact (hr ⟨False.elim, fun he => Bool.noConfusion (hc.symm.trans he)⟩).elim
  | edge he => exact (he Iff.rfl).elim
  | downstream _ hd ih =>
    obtain ⟨u, hpu, hu⟩ := ih
    rename_i p a
    rcases hd with ⟨ps, ⟨t, rfl, hdep⟩, hm⟩ | ⟨ps, ⟨t, rfl, hdep⟩, hm⟩ <;>
      · rw [List.mem_singleton] at hm
        subst hm
        exact ⟨u, .step hdep hpu, hu⟩

theorem cone_iff_reach {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) (s : σ) :
    Cone deps changed s ↔ Reach deps changed s :=
  ⟨cone_reach, reach_cone⟩

/-- A selection is sound for a graph and a change if, for every code type, every local
semantics, every per-symbol property and every pair of releases, checking the selected
symbols after the change is enough. -/
def SoundSelection {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) (R : σ → Prop) : Prop :=
  ∀ (C β : Type) (sem : (σ → C) → σ → β) (Q : σ → β → Prop) (I new : σ → C),
    Local deps sem → (∀ s, Q s (sem I s)) →
      (∀ s, R s → Q s (sem (update I changed new) s)) →
        ∀ s, Q s (sem (update I changed new) s)

/-- The cone is a sound selection (upstream `recheck_iff_scratch`). -/
theorem cone_sound {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) :
    SoundSelection deps changed (Cone deps changed) :=
  fun _ _ sem Q I new hLoc hOld hR =>
    (recheck_iff_scratch deps sem Q I changed new hLoc hOld).mp hR

/-- The witness semantics: a symbol shows a mark when a symbol it depends on carries one. -/
def markSem {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) (I : σ → Bool) (s : σ) : Prop :=
  ∃ u, DepStar deps s u ∧ changed u = true ∧ I u = true

theorem markSem_local {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) :
    Local deps (markSem deps changed) := by
  intro I I' s h
  apply propext
  constructor
  · rintro ⟨u, hu, hc, hi⟩
    exact ⟨u, hu, hc, (h u hu) ▸ hi⟩
  · rintro ⟨u, hu, hc, hi⟩
    exact ⟨u, hu, hc, (h u hu).symm ▸ hi⟩

/-- Every sound selection contains the whole cone. -/
theorem cone_least {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) (R : σ → Prop)
    (hR : SoundSelection deps changed R) : ∀ s, Cone deps changed s → R s := by
  intro s hs
  obtain ⟨u, hsu, hu⟩ := cone_reach hs
  have key := hR Bool Prop (markSem deps changed) (fun t b => R t ∨ ¬ b)
    (fun _ => false) (fun _ => true) (markSem_local deps changed)
    (fun t => Or.inr (fun ⟨_, _, _, hi⟩ => Bool.noConfusion hi))
    (fun t ht => Or.inl ht) s
  rcases key with hr | hn
  · exact hr
  · exact absurd ⟨u, hsu, hu, by simp [update, hu]⟩ hn

/-- The cone is exactly the least sound selection. -/
theorem cone_is_least_sound {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) :
    SoundSelection deps changed (Cone deps changed) ∧
      ∀ R, SoundSelection deps changed R → ∀ s, Cone deps changed s → R s :=
  ⟨cone_sound deps changed, cone_least deps changed⟩

/-! ## Below the cone: refining changes and subset-closed properties -/

/-- Component behaviors are sets of observations. -/
abbrev Bhv (ω : Type) := ω → Prop

def Sub {ω : Type} (b b' : Bhv ω) : Prop := ∀ o, b o → b' o

/-- Release behavior grows only when component behavior grows. -/
def Monotone {σ ω ω' : Type} (sem : (σ → Bhv ω) → σ → Bhv ω') : Prop :=
  ∀ I I', (∀ t, Sub (I t) (I' t)) → ∀ s, Sub (sem I s) (sem I' s)

/-- A property that survives removing behaviors. Trace safety properties are of this kind;
two-run noninterference is not. -/
def SubsetClosed {σ ω' : Type} (Q : σ → Bhv ω' → Prop) : Prop :=
  ∀ s b b', Q s b → Sub b' b → Q s b'

theorem refining_change_sound {σ ω ω' : Type} (sem : (σ → Bhv ω) → σ → Bhv ω')
    (Q : σ → Bhv ω' → Prop) (I : σ → Bhv ω) (changed : σ → Bool) (new : σ → Bhv ω)
    (hMono : Monotone sem) (hQ : SubsetClosed Q) (hOld : ∀ s, Q s (sem I s))
    (hRef : ∀ t, changed t = true → Sub (new t) (I t)) :
    ∀ s, Q s (sem (update I changed new) s) := by
  intro s
  apply hQ s _ _ (hOld s)
  apply hMono
  intro t o ho
  by_cases hc : changed t = true
  · simp [update, hc] at ho
    exact hRef t hc o ho
  · simp [update, hc] at ho
    exact ho

/-- Without monotonicity the refining change is not enough: `app` misbehaves exactly when
`lib` stops producing a value, and `lib`'s new behavior is a refinement of its old one. -/
inductive Two where
  | lib
  | app
  deriving DecidableEq

def guardSem (I : Two → Bhv Bool) : Two → Bhv Bool
  | .lib => I .lib
  | .app => fun o => o = true ∨ (o = false ∧ ¬ I .lib true)

def noFalse : Two → Bhv Bool → Prop := fun _ b => ¬ b false

theorem not_monotone_breaks :
    let I : Two → Bhv Bool := fun _ o => o = true
    let new : Two → Bhv Bool := fun _ _ => False
    let ch : Two → Bool := fun s => decide (s = .lib)
    SubsetClosed noFalse ∧ (∀ s, noFalse s (guardSem I s)) ∧
      (∀ t, ch t = true → Sub (new t) (I t)) ∧
      ¬ noFalse .app (guardSem (update I ch new) .app) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s b b' hb hsub hf
    exact hb (hsub false hf)
  · intro s
    cases s <;> simp [guardSem, noFalse]
  · intro t _ o ho
    exact ho.elim
  · simp [noFalse, guardSem, update]

theorem guardSem_not_monotone : ¬ Monotone guardSem := by
  intro h
  have := h (fun _ _ => False) (fun _ o => o = true) (fun _ _ hf => hf.elim) .app false
    (Or.inr ⟨rfl, fun hf => hf⟩)
  simp [guardSem] at this

end Family.Selection
