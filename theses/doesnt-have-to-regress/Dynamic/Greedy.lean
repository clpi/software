import Audit.Contract

namespace SoftwareDoesntRegress.Dynamic.Greedy

open SoftwareDoesntRegress.Audit

variable {Capability Outcome Key Context : Type}
  [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]

/-- Strict progress is the asymmetric part of the audited replacement
    preorder. Optional features at equal protected costs remain weakly
    publishable through `Audit.deploy`; they are not cost progress. -/
def strictImproves (q : Contract Capability Outcome Key Context)
    (old candidate : ScopedRelease Capability Outcome Key Context) : Bool :=
  replacement q old candidate && !replacement q candidate old

theorem improves_iff (q : Contract Capability Outcome Key Context)
    (old candidate : ScopedRelease Capability Outcome Key Context) :
    strictImproves q old candidate = true ↔
      replacement q old candidate = true ∧ replacement q candidate old = false := by
  simp [strictImproves, Bool.and_eq_true]

theorem improves_cost_iff (q : Contract Capability Outcome Key Context)
    (old candidate : ScopedRelease Capability Outcome Key Context) :
    strictImproves q old candidate = true ↔
      replacement q old candidate = true ∧
      ∃ k ∈ q.keys, (candidate.profile k).cost.1 < (old.profile k).cost.1 ∨
        (candidate.profile k).cost.2 < (old.profile k).cost.2 := by
  classical
  constructor
  · intro hi
    obtain ⟨hforward, hreverse⟩ := (improves_iff q old candidate).mp hi
    refine ⟨hforward, ?_⟩
    by_cases hw : ∃ k ∈ q.keys,
        (candidate.profile k).cost.1 < (old.profile k).cost.1 ∨
          (candidate.profile k).cost.2 < (old.profile k).cost.2
    · exact hw
    · have hf := (replacement_iff q old candidate).mp hforward
      have hb : replacement q candidate old = true := by
        apply (replacement_iff q candidate old).mpr
        refine ⟨hf.2.1, hf.1, ?_⟩
        intro k hk
        have hn : ¬ ((candidate.profile k).cost.1 < (old.profile k).cost.1 ∨
            (candidate.profile k).cost.2 < (old.profile k).cost.2) :=
          fun hs => hw ⟨k, hk, hs⟩
        constructor <;> omega
      simp [hreverse] at hb
  · rintro ⟨hforward, k, hk, hs⟩
    apply (improves_iff q old candidate).mpr
    refine ⟨hforward, ?_⟩
    cases hb : replacement q candidate old with
    | false => rfl
    | true =>
      have hc := ((replacement_iff q candidate old).mp hb).2.2 k hk
      rcases hc with ⟨hfirst, hsecond⟩
      omega

theorem improves_irrefl (q : Contract Capability Outcome Key Context)
    (r : ScopedRelease Capability Outcome Key Context) : strictImproves q r r = false := by
  simp [strictImproves]

theorem improves_distinct {q : Contract Capability Outcome Key Context}
    {old candidate : ScopedRelease Capability Outcome Key Context}
    (h : strictImproves q old candidate = true) : candidate ≠ old := by
  intro heq
  subst candidate
  simp [improves_irrefl] at h

theorem improves_lift {q : Contract Capability Outcome Key Context}
    {a b c : ScopedRelease Capability Outcome Key Context}
    (hab : replacement q a b = true) (hbc : strictImproves q b c = true) :
    strictImproves q a c = true := by
  obtain ⟨hbc, hn⟩ := (improves_iff q b c).mp hbc
  apply (improves_iff q a c).mpr
  refine ⟨replacement_trans hab hbc, ?_⟩
  cases hca : replacement q c a with
  | false => rfl
  | true =>
    have hcb := replacement_trans hca hab
    simp [hn] at hcb

theorem improves_trans {q : Contract Capability Outcome Key Context}
    {a b c : ScopedRelease Capability Outcome Key Context}
    (hab : strictImproves q a b = true) (hbc : strictImproves q b c = true) :
    strictImproves q a c = true :=
  improves_lift ((improves_iff q a b).mp hab).1 hbc

def greedyStep (q : Contract Capability Outcome Key Context)
    (old candidate : ScopedRelease Capability Outcome Key Context) :=
  if strictImproves q old candidate then candidate else old

theorem choose_accepts {q : Contract Capability Outcome Key Context}
    {old candidate : ScopedRelease Capability Outcome Key Context}
    (h : strictImproves q old candidate = true) : greedyStep q old candidate = candidate := by
  simp [greedyStep, h]

theorem choose_refuses {q : Contract Capability Outcome Key Context}
    {old candidate : ScopedRelease Capability Outcome Key Context}
    (h : strictImproves q old candidate = false) : greedyStep q old candidate = old := by
  simp [greedyStep, h]

theorem choose_safe {q : Contract Capability Outcome Key Context}
    {old : ScopedRelease Capability Outcome Key Context}
    (candidate : ScopedRelease Capability Outcome Key Context)
    (hold : certified q old = true) : replacement q old (greedyStep q old candidate) = true := by
  unfold greedyStep
  split
  · next h => exact ((improves_iff q old candidate).mp h).1
  · exact replacement_refl hold

theorem choose_origin (q : Contract Capability Outcome Key Context)
    (old candidate : ScopedRelease Capability Outcome Key Context) :
    greedyStep q old candidate = old ∨ greedyStep q old candidate = candidate := by
  unfold greedyStep
  split <;> simp

/-- Scan a fixed, ordered catalogue once. The output is maximal within that
    supplied catalogue, and may depend on its order across incomparable costs. -/
def greedyFrom (q : Contract Capability Outcome Key Context)
    (old : ScopedRelease Capability Outcome Key Context) :
    List (ScopedRelease Capability Outcome Key Context) →
      ScopedRelease Capability Outcome Key Context
  | [] => old
  | candidate :: tail => greedyFrom q (greedyStep q old candidate) tail

theorem sweep_safe {q : Contract Capability Outcome Key Context}
    (old : ScopedRelease Capability Outcome Key Context)
    (candidates : List (ScopedRelease Capability Outcome Key Context))
    (hold : certified q old = true) : replacement q old (greedyFrom q old candidates) = true := by
  induction candidates generalizing old with
  | nil => exact replacement_refl hold
  | cons candidate tail ih =>
    have hs := choose_safe candidate hold
    exact replacement_trans hs (ih _ ((replacement_iff q _ _).mp hs).2.1)

theorem sweep_certified {q : Contract Capability Outcome Key Context}
    (old : ScopedRelease Capability Outcome Key Context)
    (candidates : List (ScopedRelease Capability Outcome Key Context))
    (hold : certified q old = true) : certified q (greedyFrom q old candidates) = true :=
  ((replacement_iff q _ _).mp (sweep_safe old candidates hold)).2.1

theorem sweep_origin (q : Contract Capability Outcome Key Context)
    (old : ScopedRelease Capability Outcome Key Context)
    (candidates : List (ScopedRelease Capability Outcome Key Context)) :
    greedyFrom q old candidates = old ∨ greedyFrom q old candidates ∈ candidates := by
  induction candidates generalizing old with
  | nil => exact Or.inl rfl
  | cons candidate tail ih =>
    rcases ih (greedyStep q old candidate) with heq | hmem
    · rcases choose_origin q old candidate with ho | hc
      · exact Or.inl (heq.trans ho)
      · exact Or.inr (List.mem_cons.mpr (Or.inl (heq.trans hc)))
    · exact Or.inr (List.mem_cons_of_mem candidate hmem)

theorem sweep_maximal {q : Contract Capability Outcome Key Context}
    (old : ScopedRelease Capability Outcome Key Context)
    (candidates : List (ScopedRelease Capability Outcome Key Context))
    (hold : certified q old = true) :
    ∀ candidate ∈ candidates, strictImproves q (greedyFrom q old candidates) candidate = false := by
  induction candidates generalizing old with
  | nil => intro candidate hmem; cases hmem
  | cons candidate tail ih =>
    intro other hmem
    have hchosen := choose_safe candidate hold
    have hcert := ((replacement_iff q _ _).mp hchosen).2.1
    have htail := sweep_safe (greedyStep q old candidate) tail hcert
    rcases List.mem_cons.mp hmem with rfl | hmem
    · cases htry : strictImproves q old other with
      | true =>
        rw [greedyFrom, choose_accepts htry]
        have hs := sweep_safe other tail
          ((replacement_iff q old other).mp ((improves_iff q old other).mp htry).1).2.1
        cases hback : strictImproves q (greedyFrom q other tail) other with
        | false => rfl
        | true =>
          have hn := ((improves_iff q _ _).mp hback).2
          simp [hs] at hn
      | false =>
        rw [greedyFrom, choose_refuses htry]
        cases hout : strictImproves q (greedyFrom q old tail) other with
        | false => rfl
        | true =>
          have hbad := improves_lift (sweep_safe old tail hold) hout
          simp [htry] at hbad
    · exact ih (greedyStep q old candidate) hcert other hmem

theorem sweep_append (q : Contract Capability Outcome Key Context)
    (old : ScopedRelease Capability Outcome Key Context)
    (first later : List (ScopedRelease Capability Outcome Key Context)) :
    greedyFrom q old (first ++ later) = greedyFrom q (greedyFrom q old first) later := by
  induction first generalizing old with
  | nil => rfl
  | cons candidate tail ih =>
    exact ih (greedyStep q old candidate)

theorem sweep_progress {q : Contract Capability Outcome Key Context}
    (old : ScopedRelease Capability Outcome Key Context)
    (candidates : List (ScopedRelease Capability Outcome Key Context))
    (hold : certified q old = true)
    (hex : ∃ candidate ∈ candidates, strictImproves q old candidate = true) :
    strictImproves q old (greedyFrom q old candidates) = true := by
  apply (improves_iff q _ _).mpr
  refine ⟨sweep_safe old candidates hold, ?_⟩
  cases hback : replacement q (greedyFrom q old candidates) old with
  | false => rfl
  | true =>
    obtain ⟨candidate, hmem, hc⟩ := hex
    have hbad := improves_lift hback hc
    simp [sweep_maximal old candidates hold candidate hmem] at hbad

theorem sweep_stable (q : Contract Capability Outcome Key Context)
    (old : ScopedRelease Capability Outcome Key Context)
    (candidates : List (ScopedRelease Capability Outcome Key Context))
    (h : ∀ candidate ∈ candidates, strictImproves q old candidate = false) :
    greedyFrom q old candidates = old := by
  induction candidates with
  | nil => rfl
  | cons candidate tail ih =>
    rw [greedyFrom, choose_refuses (h candidate (by simp))]
    exact ih (fun c hc => h c (List.mem_cons_of_mem candidate hc))

theorem rescan_idempotent {q : Contract Capability Outcome Key Context}
    (old : ScopedRelease Capability Outcome Key Context)
    (candidates : List (ScopedRelease Capability Outcome Key Context))
    (hold : certified q old = true) :
    greedyFrom q (greedyFrom q old candidates) candidates = greedyFrom q old candidates :=
  sweep_stable q _ candidates (sweep_maximal old candidates hold)

/-- Counts candidate attempts, not primitive checks or elapsed runtime. -/
def countedSweep (q : Contract Capability Outcome Key Context)
    (old : ScopedRelease Capability Outcome Key Context) :
    List (ScopedRelease Capability Outcome Key Context) →
      ScopedRelease Capability Outcome Key Context × Nat
  | [] => (old, 0)
  | candidate :: tail =>
    let result := countedSweep q (greedyStep q old candidate) tail
    (result.1, result.2 + 1)

theorem counted_sweep_exact (q : Contract Capability Outcome Key Context)
    (old : ScopedRelease Capability Outcome Key Context)
    (candidates : List (ScopedRelease Capability Outcome Key Context)) :
    (countedSweep q old candidates).1 = greedyFrom q old candidates ∧
    (countedSweep q old candidates).2 = candidates.length := by
  induction candidates generalizing old with
  | nil => exact ⟨rfl, rfl⟩
  | cons candidate tail ih =>
    obtain ⟨hr, hc⟩ := ih (greedyStep q old candidate)
    exact ⟨hr, congrArg (fun n => n + 1) hc⟩

structure Archive (Capability Outcome Key Context : Type) where
  incumbent : ScopedRelease Capability Outcome Key Context
  candidates : List (ScopedRelease Capability Outcome Key Context)

def start (old : ScopedRelease Capability Outcome Key Context) :
    Archive Capability Outcome Key Context := ⟨old, [old]⟩

/-- Append-only arrival processing under one fixed contract. Reusing a prior
    maximality certificate requires that same contract, including its content. -/
def arrive (q : Contract Capability Outcome Key Context)
    (state : Archive Capability Outcome Key Context)
    (news : List (ScopedRelease Capability Outcome Key Context)) :
    Archive Capability Outcome Key Context :=
  { incumbent := greedyFrom q state.incumbent news
    candidates := state.candidates ++ news }

def Maximal (q : Contract Capability Outcome Key Context)
    (state : Archive Capability Outcome Key Context) : Prop :=
  ∀ candidate ∈ state.candidates, strictImproves q state.incumbent candidate = false

theorem arrive_keeps_archive (q : Contract Capability Outcome Key Context)
    (state : Archive Capability Outcome Key Context)
    (news : List (ScopedRelease Capability Outcome Key Context)) :
    ∀ candidate ∈ state.candidates, candidate ∈ (arrive q state news).candidates := by
  intro candidate hmem
  exact List.mem_append.mpr (Or.inl hmem)

theorem arrive_incumbent_archived (q : Contract Capability Outcome Key Context)
    (state : Archive Capability Outcome Key Context)
    (news : List (ScopedRelease Capability Outcome Key Context))
    (h : state.incumbent ∈ state.candidates) :
    (arrive q state news).incumbent ∈ (arrive q state news).candidates := by
  rcases sweep_origin q state.incumbent news with hold | hnew
  · apply List.mem_append.mpr
    apply Or.inl
    change greedyFrom q state.incumbent news ∈ state.candidates
    rw [hold]
    exact h
  · exact List.mem_append.mpr (Or.inr hnew)

theorem arrive_safe {q : Contract Capability Outcome Key Context}
    (state : Archive Capability Outcome Key Context)
    (news : List (ScopedRelease Capability Outcome Key Context))
    (hcert : certified q state.incumbent = true) :
    replacement q state.incumbent (arrive q state news).incumbent = true :=
  sweep_safe state.incumbent news hcert

theorem arrive_maximal {q : Contract Capability Outcome Key Context}
    (state : Archive Capability Outcome Key Context)
    (news : List (ScopedRelease Capability Outcome Key Context))
    (hcert : certified q state.incumbent = true) (hmax : Maximal q state) :
    Maximal q (arrive q state news) := by
  intro candidate hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · cases htry : strictImproves q (arrive q state news).incumbent candidate with
    | false => rfl
    | true =>
      have hbad := improves_lift (arrive_safe state news hcert) htry
      simp [hmax candidate hold] at hbad
  · exact sweep_maximal state.incumbent news hcert candidate hnew

/-- Recheck the incumbent and rescan the complete retained archive under the
    current contract. Invalidating the incumbent blocks normal replacement;
    a separate, explicit recovery operation must establish a fresh baseline. -/
def reconsider (q : Contract Capability Outcome Key Context)
    (state : Archive Capability Outcome Key Context) :
    Option (Archive Capability Outcome Key Context) :=
  if certified q state.incumbent then
    some { incumbent := greedyFrom q state.incumbent state.candidates
           candidates := state.candidates }
  else none

theorem reconsider_safe {q : Contract Capability Outcome Key Context}
    {state result : Archive Capability Outcome Key Context}
    (h : reconsider q state = some result) :
    replacement q state.incumbent result.incumbent = true ∧
    result.candidates = state.candidates ∧ Maximal q result := by
  unfold reconsider at h
  split at h
  · next hc =>
    have heq := Option.some.inj h
    subst result
    exact ⟨sweep_safe state.incumbent state.candidates hc, rfl,
      sweep_maximal state.incumbent state.candidates hc⟩
  · contradiction

theorem reconsider_invalid_blocks {q : Contract Capability Outcome Key Context}
    (state : Archive Capability Outcome Key Context)
    (h : certified q state.incumbent = false) : reconsider q state = none := by
  simp [reconsider, h]

def timeline (q : Contract Capability Outcome Key Context)
    (initial : ScopedRelease Capability Outcome Key Context)
    (arrivals : Nat → List (ScopedRelease Capability Outcome Key Context)) :
    Nat → ScopedRelease Capability Outcome Key Context
  | 0 => initial
  | n + 1 => greedyFrom q (timeline q initial arrivals n) (arrivals n)

theorem timeline_certified {q : Contract Capability Outcome Key Context}
    (initial : ScopedRelease Capability Outcome Key Context)
    (arrivals : Nat → List (ScopedRelease Capability Outcome Key Context))
    (h : certified q initial = true) (n : Nat) :
    certified q (timeline q initial arrivals n) = true := by
  induction n with
  | zero => exact h
  | succ n ih => exact sweep_certified _ _ ih

theorem timeline_add {q : Contract Capability Outcome Key Context}
    (initial : ScopedRelease Capability Outcome Key Context)
    (arrivals : Nat → List (ScopedRelease Capability Outcome Key Context))
    (h : certified q initial = true) (m d : Nat) :
    replacement q (timeline q initial arrivals m) (timeline q initial arrivals (m + d)) = true := by
  induction d with
  | zero => exact replacement_refl (timeline_certified initial arrivals h m)
  | succ d ih =>
    exact replacement_trans ih
      (sweep_safe _ _ (timeline_certified initial arrivals h (m + d)))

theorem timeline_chain {q : Contract Capability Outcome Key Context}
    (initial : ScopedRelease Capability Outcome Key Context)
    (arrivals : Nat → List (ScopedRelease Capability Outcome Key Context))
    (h : certified q initial = true) {m n : Nat} (hmn : m ≤ n) :
    replacement q (timeline q initial arrivals m) (timeline q initial arrivals n) = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact timeline_add initial arrivals h m d

/-- Enumerate every include/exclude choice in a fixed execution order, retaining
    duplicates. A head edit runs after the selected tail edits. This covers no
    omitted edit, alternative order, or unbounded search space. -/
def bundles {α : Type} (seed : α) : List (α → α) → List α
  | [] => [seed]
  | edit :: edits =>
    let tail := bundles seed edits
    tail ++ tail.map edit

theorem bundle_count {α : Type} (seed : α) (edits : List (α → α)) :
    (bundles seed edits).length = 2 ^ edits.length := by
  induction edits with
  | nil => rfl
  | cons edit edits ih =>
    simp only [bundles, List.length_append, List.length_map, List.length_cons, ih]
    omega

theorem bundle_keeps_seed {α : Type} (seed : α) (edits : List (α → α)) :
    seed ∈ bundles seed edits := by
  induction edits with
  | nil => simp [bundles]
  | cons edit edits ih => exact List.mem_append.mpr (Or.inl ih)

def applyChoices {α : Type} (seed : α) : List (Bool × (α → α)) → α
  | [] => seed
  | (enabled, edit) :: edits =>
    let tail := applyChoices seed edits
    if enabled then edit tail else tail

theorem every_bundle_choice_present {α : Type} (seed : α)
    (choices : List (Bool × (α → α))) :
    applyChoices seed choices ∈ bundles seed (choices.map Prod.snd) := by
  induction choices with
  | nil => simp [applyChoices, bundles]
  | cons choice choices ih =>
    rcases choice with ⟨enabled, edit⟩
    cases enabled with
    | false => exact List.mem_append.mpr (Or.inl ih)
    | true => exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, ih, rfl⟩))

theorem bundle_greedy_maximal {q : Contract Capability Outcome Key Context}
    (old : ScopedRelease Capability Outcome Key Context)
    (edits : List (ScopedRelease Capability Outcome Key Context →
      ScopedRelease Capability Outcome Key Context))
    (hold : certified q old = true) :
    ∀ candidate ∈ bundles old edits,
      strictImproves q (greedyFrom q old (bundles old edits)) candidate = false :=
  sweep_maximal old (bundles old edits) hold

end SoftwareDoesntRegress.Dynamic.Greedy
