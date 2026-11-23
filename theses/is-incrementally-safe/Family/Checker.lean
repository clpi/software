import Family.Dataflow

/-!
# An executable checker that is the thing the theorems are about

Upstream status: master's `check` concludes `ReleaseSafe` only for `releaseOf p`, a one-symbol
release built from the patch; the whole-release cone checker (`incrCheck`) lives only in the
draft PR to the idol branch and takes an untrusted cone witness. This module gives a checker
over the master model that:

* computes the recheck set itself from the spec's dependency list (`coneK`), so nothing the
  submitter supplies is trusted, and re-verifies its closure (fail-closed);
* is sound for the whole release (`incrCheck_sound`);
* equals the whole-snapshot check whenever the computed set is closed (`incr_eq_full`), which
  connects the incremental verdict to full-snapshot acceptance in one theorem;
* never rechecks more than the cone (`coneK_sub_cone`), so a closed `coneK` is exactly the
  cone (`coneK_eq_cone`), the least sound selection by `cone_least`.

Premises, all named: `Local` (or a dataflow semantics, where it is proven), the old release
passing, `syms` listing every symbol, and `chk` deciding the spec `Q`. Trust boundary: the
dependency list and `Q` come from whoever writes the spec. A spec that omits an edge or that
accepts everything makes the checker accept a bad release; that is `missing_edge_cone_passes`
and `SpecAuthority` upstream. `Family.CheckerClosure` proves that `syms.length + 1` rounds always reach closure
(`coneK_closed`), which removes the closure side condition (`incr_eq_full'`, `coneK_eq_cone'`).
-/
namespace Family.Checker

open Family.Dataflow Family.Selection SoftwareIsIncrementallySafe.OrderedIncrement

variable {σ C β : Type} [DecidableEq σ]

def DepsL (deps : List (σ × σ)) : σ → σ → Prop := fun s t => (s, t) ∈ deps

def stepK (deps : List (σ × σ)) (syms K : List σ) : List σ :=
  K ++ syms.filter (fun s => !K.contains s && deps.any (fun e => e.1 == s && K.contains e.2))

def iterK (deps : List (σ × σ)) (syms : List σ) : Nat → List σ → List σ
  | 0, K => K
  | n + 1, K => iterK deps syms n (stepK deps syms K)

def coneK (deps : List (σ × σ)) (syms changed : List σ) : List σ :=
  iterK deps syms (syms.length + 1) changed

def closedB (deps : List (σ × σ)) (changed K : List σ) : Bool :=
  changed.all (fun c => K.contains c) && deps.all (fun e => !K.contains e.2 || K.contains e.1)

def chOf (changed : List σ) : σ → Bool := fun s => changed.contains s

def incrCheck (deps : List (σ × σ)) (syms changed : List σ) (chk : σ → β → Bool)
    (sem : (σ → C) → σ → β) (I new : σ → C) : Bool :=
  let K := coneK deps syms changed
  closedB deps changed K && K.all (fun s => chk s (sem (update I (chOf changed) new) s))

def fullCheck (syms changed : List σ) (chk : σ → β → Bool) (sem : (σ → C) → σ → β)
    (I new : σ → C) : Bool :=
  syms.all (fun s => chk s (sem (update I (chOf changed) new) s))

theorem closedB_spec {deps : List (σ × σ)} {changed K : List σ}
    (h : closedB deps changed K = true) :
    (∀ s, chOf changed s = true → s ∈ K) ∧ (∀ s t, DepsL deps s t → t ∈ K → s ∈ K) := by
  simp only [closedB, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun s hs => ?_, fun s t hst ht => ?_⟩
  · simpa [chOf] using h.1 s (by simpa [chOf] using hs)
  · have := h.2 _ hst
    simp at this
    rcases this with h' | h'
    · exact absurd ht h'
    · exact h'

theorem incrCheck_sound (deps : List (σ × σ)) (syms changed : List σ) (chk : σ → β → Bool)
    (Q : σ → β → Prop) (hchk : ∀ s b, chk s b = true → Q s b)
    (sem : (σ → C) → σ → β) (I new : σ → C) (hLoc : Local (DepsL deps) sem)
    (hOld : ∀ s, Q s (sem I s)) (hAcc : incrCheck deps syms changed chk sem I new = true) :
    ∀ s, Q s (sem (update I (chOf changed) new) s) := by
  simp only [incrCheck, Bool.and_eq_true, List.all_eq_true] at hAcc
  obtain ⟨hc, hd⟩ := closedB_spec hAcc.1
  exact closed_witness_sound (fun s => s ∈ coneK deps syms changed) hc hd hLoc hOld
    (fun s hs => hchk s _ (hAcc.2 s hs))

/-- Every member of the computed set reaches a changed symbol. -/
theorem iterK_reach (deps : List (σ × σ)) (syms changed : List σ) :
    ∀ n K, (∀ s, s ∈ K → Reach (DepsL deps) (chOf changed) s) →
      ∀ s, s ∈ iterK deps syms n K → Reach (DepsL deps) (chOf changed) s
  | 0, _, h => h
  | n + 1, K, h => by
    apply iterK_reach deps syms changed n
    intro s hs
    simp only [stepK, List.mem_append, List.mem_filter, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq, List.contains_iff_mem] at hs
    rcases hs with hs | ⟨_, _, e, he, rfl, ht⟩
    · exact h s hs
    · obtain ⟨u, hu, hcu⟩ := h e.2 ht
      exact ⟨u, .step (show DepsL deps e.1 e.2 from he) hu, hcu⟩

theorem coneK_sub_cone (deps : List (σ × σ)) (syms changed : List σ) (s : σ)
    (hs : s ∈ coneK deps syms changed) : Cone (DepsL deps) (chOf changed) s :=
  reach_cone (iterK_reach deps syms changed _ changed
    (fun c hc => ⟨c, .refl c, by simp [chOf, hc]⟩) s hs)

theorem coneK_eq_cone (deps : List (σ × σ)) (syms changed : List σ)
    (hcl : closedB deps changed (coneK deps syms changed) = true) (s : σ) :
    s ∈ coneK deps syms changed ↔ Cone (DepsL deps) (chOf changed) s := by
  obtain ⟨hc, hd⟩ := closedB_spec hcl
  exact ⟨coneK_sub_cone deps syms changed s, cone_sub_closed _ hc hd s⟩

/-- The incremental verdict is the whole-snapshot verdict whenever the computed set is
closed. -/
theorem incr_eq_full (deps : List (σ × σ)) (syms changed : List σ) (hsyms : ∀ s, s ∈ syms)
    (chk : σ → β → Bool) (sem : (σ → C) → σ → β) (I new : σ → C)
    (hLoc : Local (DepsL deps) sem) (hOld : ∀ s, chk s (sem I s) = true)
    (hcl : closedB deps changed (coneK deps syms changed) = true) :
    incrCheck deps syms changed chk sem I new = fullCheck syms changed chk sem I new := by
  obtain ⟨hc, hd⟩ := closedB_spec hcl
  apply Bool.eq_iff_iff.mpr
  simp only [incrCheck, fullCheck, hcl, Bool.true_and, List.all_eq_true]
  constructor
  · intro hK s _
    exact closed_witness_sound (Q := fun s b => chk s b = true)
      (fun s => s ∈ coneK deps syms changed) hc hd hLoc hOld hK s
  · intro hall s _
    exact hall s (hsyms s)

/-! ## Executable demonstration: a build graph with numeric artifacts -/

inductive Unit' where
  | core | net | ui | cli | docs
  deriving DecidableEq, Repr

def demoSyms : List Unit' := [.core, .net, .ui, .cli, .docs]
def demoDeps : List (Unit' × Unit') := [(.net, .core), (.ui, .net), (.cli, .net), (.docs, .core)]

/-- Each unit's artifact: its own number plus its dependencies' artifacts. -/
def demoStep (s : Unit') (c : Nat) (f : Unit' → Nat) : Nat :=
  c + demoSyms.foldr (fun t acc => (if demoDeps.contains (s, t) then f t else 0) + acc) 0

def depB (s t : Unit') : Bool := demoDeps.contains (s, t)

def demoSem (I : Unit' → Nat) (s : Unit') : Nat := run depB demoStep 0 I 4 s

/-- The spec: every artifact stays under a size budget. -/
def demoChk (_ : Unit') (b : Nat) : Bool := b ≤ 20

def demoOld : Unit' → Nat := fun _ => 2

theorem demo_local : Local (DepsL demoDeps) demoSem := by
  have h := dataflow_local depB demoStep 0 4
  intro I I' s hagree
  exact h I I' s (fun t ht => hagree t (by
    clear hagree h
    induction ht with
    | refl => exact .refl _
    | step hd _ ih => exact .step (by simpa [DepsL, Deps, depB] using hd) ih))

example : demoSyms.all (fun s => demoChk s (demoSem demoOld s)) = true := by decide

/-- Changing `net` rechecks `net`, `ui`, `cli` only. -/
example : coneK demoDeps demoSyms [.net] = [.net, .ui, .cli] := by decide

example : closedB demoDeps [.net] (coneK demoDeps demoSyms [.net]) = true := by decide

/-- A small growth of `net` is admitted by the incremental check. -/
example : incrCheck demoDeps demoSyms [.net] demoChk demoSem demoOld (fun _ => 5) = true := by
  decide

/-- A growth that pushes `ui` over budget is refused, though `net` alone stays under it. -/
example : demoChk .net (demoSem (update demoOld (chOf [.net]) (fun _ => 18)) .net) = true ∧
    incrCheck demoDeps demoSyms [.net] demoChk demoSem demoOld (fun _ => 18) = false := by
  decide

end Family.Checker
