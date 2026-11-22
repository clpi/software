import Dynamic.Incremental
import Dynamic.Greedy
import Dynamic.Evolution

namespace SoftwareDoesntRegress.Dynamic.Engine

open SoftwareDoesntRegress.Audit

variable {Capability Outcome Key Context : Type}
  [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Key] [DecidableEq Context]

structure Artifact (Capability Outcome Key Context : Type) where
  id : Nat
  release : ScopedRelease Capability Outcome Key Context

structure SweepResult (Capability Outcome Key Context : Type)
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context] where
  incumbent : Artifact Capability Outcome Key Context
  cache : Incremental.Cache Capability Outcome Key Context
  evaluated : Nat
  reused : Nat

/-- Greedy selection uses the same certified incremental evaluator in both
directions. Equivalent releases are not strict improvements. -/
def choose (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context) :
    SweepResult Capability Outcome Key Context :=
  let forward := Incremental.recertify cache q old.release candidate.release
  let backward := Incremental.recertify forward.cache q candidate.release old.release
  { incumbent := if forward.verdict && !backward.verdict then candidate else old
    cache := backward.cache
    evaluated := forward.evaluated + backward.evaluated
    reused := forward.reused + backward.reused }

theorem choose_exact (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context) :
    (choose q cache old candidate).incumbent.release =
      Greedy.greedyStep q old.release candidate.release := by
  simp only [choose, Incremental.verdict_eq, Greedy.greedyStep, Greedy.strictImproves]
  split <;> rfl

theorem choose_origin (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context) :
    (choose q cache old candidate).incumbent = old ∨
      (choose q cache old candidate).incumbent = candidate := by
  simp only [choose]
  split <;> simp

theorem choose_prefix (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context) :
    ∃ suffix, (choose q cache old candidate).cache = cache ++ suffix := by
  obtain ⟨first, hf⟩ := Incremental.recertify_prefix cache q old.release candidate.release
  obtain ⟨rest, hr⟩ := Incremental.recertify_prefix
    (Incremental.recertify cache q old.release candidate.release).cache q
    candidate.release old.release
  exact ⟨first ++ rest, by simp only [choose]; rw [hr, hf, List.append_assoc]⟩

def sweep (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old : Artifact Capability Outcome Key Context) :
    List (Artifact Capability Outcome Key Context) → SweepResult Capability Outcome Key Context
  | [] => ⟨old, cache, 0, 0⟩
  | candidate :: rest =>
    let first := choose q cache old candidate
    let later := sweep q first.cache first.incumbent rest
    { incumbent := later.incumbent, cache := later.cache
      evaluated := first.evaluated + later.evaluated
      reused := first.reused + later.reused }

theorem sweep_exact (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old : Artifact Capability Outcome Key Context)
    (candidates : List (Artifact Capability Outcome Key Context)) :
    (sweep q cache old candidates).incumbent.release =
      Greedy.greedyFrom q old.release (candidates.map Artifact.release) := by
  induction candidates generalizing cache old with
  | nil => rfl
  | cons candidate rest ih =>
    simp only [sweep, List.map_cons, Greedy.greedyFrom, ih, choose_exact]

theorem sweep_safe (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old : Artifact Capability Outcome Key Context)
    (candidates : List (Artifact Capability Outcome Key Context))
    (hc : certified q old.release = true) :
    replacement q old.release (sweep q cache old candidates).incumbent.release = true := by
  rw [sweep_exact]
  exact Greedy.sweep_safe _ _ hc

theorem sweep_maximal (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old : Artifact Capability Outcome Key Context)
    (candidates : List (Artifact Capability Outcome Key Context))
    (hc : certified q old.release = true) :
    ∀ candidate ∈ candidates,
      Greedy.strictImproves q (sweep q cache old candidates).incumbent.release
        candidate.release = false := by
  intro candidate hm
  rw [sweep_exact]
  exact Greedy.sweep_maximal _ _ hc _ (List.mem_map.mpr ⟨candidate, hm, rfl⟩)

theorem sweep_origin (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old : Artifact Capability Outcome Key Context)
    (candidates : List (Artifact Capability Outcome Key Context)) :
    (sweep q cache old candidates).incumbent = old ∨
      (sweep q cache old candidates).incumbent ∈ candidates := by
  induction candidates generalizing cache old with
  | nil => exact Or.inl rfl
  | cons candidate rest ih =>
    rcases ih (choose q cache old candidate).cache
      (choose q cache old candidate).incumbent with heq | hm
    · rcases choose_origin q cache old candidate with ho | hn
      · exact Or.inl (heq.trans ho)
      · exact Or.inr (List.mem_cons.mpr (Or.inl (heq.trans hn)))
    · exact Or.inr (List.mem_cons_of_mem candidate hm)

theorem sweep_prefix (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old : Artifact Capability Outcome Key Context)
    (candidates : List (Artifact Capability Outcome Key Context)) :
    ∃ suffix, (sweep q cache old candidates).cache = cache ++ suffix := by
  induction candidates generalizing cache old with
  | nil => exact ⟨[], (List.append_nil cache).symm⟩
  | cons candidate rest ih =>
    obtain ⟨first, hf⟩ := choose_prefix q cache old candidate
    obtain ⟨later, hl⟩ := ih (choose q cache old candidate).cache
      (choose q cache old candidate).incumbent
    exact ⟨first ++ later, by simp only [sweep]; rw [hl, hf, List.append_assoc]⟩

structure Attempt (Capability Outcome Key Context : Type)
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    extends SweepResult Capability Outcome Key Context where
  accepted : Bool

/-- Explicit publication and rollback allow equivalence as well as strict gain. -/
def publish (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context) :
    Attempt Capability Outcome Key Context :=
  let checked := Incremental.recertify cache q old.release candidate.release
  { incumbent := if checked.verdict then candidate else old
    cache := checked.cache, evaluated := checked.evaluated, reused := checked.reused
    accepted := checked.verdict }

theorem publish_exact (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context) :
    (publish q cache old candidate).accepted = replacement q old.release candidate.release :=
  Incremental.verdict_eq cache q old.release candidate.release

theorem publish_safe (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context)
    (hc : certified q old.release = true) :
    replacement q old.release (publish q cache old candidate).incumbent.release = true := by
  simp only [publish, Incremental.verdict_eq]
  split
  · assumption
  · exact replacement_refl hc

omit [DecidableEq Key] in
theorem self_replacement_eq (q : Contract Capability Outcome Key Context)
    (r : ScopedRelease Capability Outcome Key Context) : replacement q r r = certified q r := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨fun h => ((replacement_iff q r r).mp h).1, replacement_refl⟩

/-- Public search blocks invalid baselines even with an empty candidate list.
The raw sweep is useful inside an already certified state invariant. -/
def select (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old : Artifact Capability Outcome Key Context)
    (candidates : List (Artifact Capability Outcome Key Context)) :
    Option (SweepResult Capability Outcome Key Context) :=
  let baseline := Incremental.recertify cache q old.release old.release
  if baseline.verdict then
    let selected := sweep q baseline.cache old candidates
    some { selected with evaluated := baseline.evaluated + selected.evaluated
                         reused := baseline.reused + selected.reused }
  else none

theorem select_safe {q : Contract Capability Outcome Key Context}
    {cache : Incremental.Cache Capability Outcome Key Context}
    {old : Artifact Capability Outcome Key Context}
    {candidates : List (Artifact Capability Outcome Key Context)}
    {result : SweepResult Capability Outcome Key Context}
    (h : select q cache old candidates = some result) :
    replacement q old.release result.incumbent.release = true := by
  simp only [select] at h
  split at h
  · next hc =>
    rw [Incremental.verdict_eq, self_replacement_eq] at hc
    have heq := Option.some.inj h
    subst result
    exact sweep_safe q _ old candidates hc
  · contradiction

theorem select_maximal {q : Contract Capability Outcome Key Context}
    {cache : Incremental.Cache Capability Outcome Key Context}
    {old : Artifact Capability Outcome Key Context}
    {candidates : List (Artifact Capability Outcome Key Context)}
    {result : SweepResult Capability Outcome Key Context}
    (h : select q cache old candidates = some result) :
    ∀ candidate ∈ candidates,
      Greedy.strictImproves q result.incumbent.release candidate.release = false := by
  simp only [select] at h
  split at h
  · next hc =>
    rw [Incremental.verdict_eq, self_replacement_eq] at hc
    have heq := Option.some.inj h
    subst result
    exact sweep_maximal q _ old candidates hc
  · contradiction

theorem select_invalid_blocks (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old : Artifact Capability Outcome Key Context)
    (candidates : List (Artifact Capability Outcome Key Context))
    (hc : certified q old.release = false) : select q cache old candidates = none := by
  simp [select, Incremental.verdict_eq, self_replacement_eq, hc]

/-- Checked publication does not present an invalid incumbent as a fallback. -/
def deploy (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context) :
    Option (Attempt Capability Outcome Key Context) :=
  let baseline := Incremental.recertify cache q old.release old.release
  if baseline.verdict then
    let attempted := publish q baseline.cache old candidate
    some { attempted with evaluated := baseline.evaluated + attempted.evaluated
                          reused := baseline.reused + attempted.reused }
  else none

theorem deploy_safe {q : Contract Capability Outcome Key Context}
    {cache : Incremental.Cache Capability Outcome Key Context}
    {old candidate : Artifact Capability Outcome Key Context}
    {result : Attempt Capability Outcome Key Context}
    (h : deploy q cache old candidate = some result) :
    replacement q old.release result.incumbent.release = true := by
  simp only [deploy] at h
  split at h
  · next hc =>
    rw [Incremental.verdict_eq, self_replacement_eq] at hc
    have heq := Option.some.inj h
    subst result
    exact publish_safe q _ old candidate hc
  · contradiction

theorem deploy_invalid_blocks (q : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context)
    (hc : certified q old.release = false) : deploy q cache old candidate = none := by
  simp [deploy, Incremental.verdict_eq, self_replacement_eq, hc]

/-- A dynamic commit recycles the old admission proof and establishes only
the newly missing judgments for the strengthened contract. -/
def adopt (oldQ nextQ : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context) :
    Attempt Capability Outcome Key Context :=
  let prior := Incremental.recertify cache oldQ old.release candidate.release
  let next := Incremental.recertify prior.cache nextQ candidate.release candidate.release
  let accepted := prior.verdict && Evolution.strengthens oldQ nextQ && next.verdict
  { incumbent := if accepted then candidate else old
    cache := next.cache, evaluated := prior.evaluated + next.evaluated
    reused := prior.reused + next.reused, accepted := accepted }

theorem adopt_exact (oldQ nextQ : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context) :
    (adopt oldQ nextQ cache old candidate).accepted =
      Evolution.admissible ⟨oldQ, old.release⟩ ⟨nextQ, candidate.release⟩ := by
  simp only [adopt, Incremental.verdict_eq, self_replacement_eq, Evolution.admissible]

theorem adopt_safe (oldQ nextQ : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context)
    (ha : (adopt oldQ nextQ cache old candidate).accepted = true) :
    Evolution.admissible ⟨oldQ, old.release⟩
      ⟨nextQ, (adopt oldQ nextQ cache old candidate).incumbent.release⟩ = true := by
  have he := ha
  rw [adopt_exact] at he
  have hi : (adopt oldQ nextQ cache old candidate).incumbent = candidate := by
    simp only [adopt] at ha ⊢
    rw [if_pos ha]
  rw [hi]
  exact he

/-- Automatic archive reconsideration after strengthening composes with the
admitting feature's proof; it cannot discard the older contract. -/
theorem adoption_then_selection_safe
    (oldQ nextQ : Contract Capability Outcome Key Context)
    (cache : Incremental.Cache Capability Outcome Key Context)
    (old candidate : Artifact Capability Outcome Key Context)
    (candidates : List (Artifact Capability Outcome Key Context))
    {selected : SweepResult Capability Outcome Key Context}
    (ha : (adopt oldQ nextQ cache old candidate).accepted = true)
    (hs : select nextQ (adopt oldQ nextQ cache old candidate).cache
      (adopt oldQ nextQ cache old candidate).incumbent candidates = some selected) :
    Evolution.admissible ⟨oldQ, old.release⟩ ⟨nextQ, selected.incumbent.release⟩ = true := by
  have hadopt := adopt_safe oldQ nextQ cache old candidate ha
  have hselect := select_safe hs
  apply Evolution.admissible_trans hadopt
  exact (Evolution.admissible_iff _ _).mpr
    ⟨hselect, Evolution.strengthens_refl nextQ,
      ((replacement_iff nextQ _ _).mp hselect).2.1⟩

end SoftwareDoesntRegress.Dynamic.Engine
