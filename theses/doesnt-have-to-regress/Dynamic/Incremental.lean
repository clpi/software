import Audit.Contract

namespace SoftwareDoesntRegress.Dynamic.Incremental

open SoftwareIsQuantifiable.Pareto
open SoftwareDoesntRegress.Audit

/- Exact structural inputs, rather than a name, revision number, or digest, bind
   every receipt to its judgment. Contexts remain part of local stamps even
   when the local predicate itself does not inspect them. -/
inductive Stamp (Capability Outcome Key Context : Type) where
  | context (expected actual : Context)
  | capability (expected actual : Context) (key : Key)
      (required offered : List Capability)
  | outcome (expected actual : Context) (key : Key)
      (allowed possible : List Outcome)
  | cost (expected oldContext newContext : Context) (key : Key)
      (old new : Point)
  deriving DecidableEq

variable {Capability Outcome Key Context : Type}
variable [DecidableEq Capability] [DecidableEq Outcome]
variable [DecidableEq Context]

def evaluate : Stamp Capability Outcome Key Context → Bool
  | .context expected actual => decide (actual = expected)
  | .capability _ _ _ required offered =>
      noQualifiedBehaviorLost ⟨required⟩ ⟨offered⟩
  | .outcome _ _ _ allowed possible =>
      possible.all fun o => decide (o ∈ allowed)
  | .cost _ _ _ _ old new => decide (noWorse new old)

def Judgment : Stamp Capability Outcome Key Context → Prop
  | .context expected actual => actual = expected
  | .capability _ _ _ required offered => ∀ b ∈ required, b ∈ offered
  | .outcome _ _ _ allowed possible => ∀ o ∈ possible, o ∈ allowed
  | .cost _ _ _ _ old new => noWorse new old

theorem evaluate_iff (s : Stamp Capability Outcome Key Context) :
    evaluate s = true ↔ Judgment s := by
  cases s <;> simp [evaluate, Judgment, noQualifiedBehaviorLost_iff, List.all_eq_true]

def keyTasks (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) (k : Key) :
    List (Stamp Capability Outcome Key Context) :=
  [ .capability q.context old.context k (q.prior k).qualified
      (old.profile k).offered.offered,
    .outcome q.context old.context k (q.allowed k) (old.profile k).possible,
    .capability q.context new.context k (q.prior k).qualified
      (new.profile k).offered.offered,
    .outcome q.context new.context k (q.allowed k) (new.profile k).possible,
    .cost q.context old.context new.context k
      (old.profile k).cost (new.profile k).cost ]

def tasks (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    List (Stamp Capability Outcome Key Context) :=
  [.context q.context old.context, .context q.context new.context] ++
    q.keys.flatMap (keyTasks q old new)

omit [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context] in
theorem tasks_length (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    (tasks q old new).length = 2 + 5 * q.keys.length := by
  simp only [tasks, List.length_append, List.length_cons, List.length_nil]
  have h : (q.keys.flatMap (keyTasks q old new)).length = 5 * q.keys.length := by
    induction q.keys with
    | nil => rfl
    | cons k ks ih =>
        simp only [List.flatMap_cons, List.length_append, keyTasks,
          List.length_cons, List.length_nil] at ih ⊢
        omega
  omega

theorem tasks_exact (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    (tasks q old new).all evaluate = replacement q old new := by
  apply Bool.eq_iff_iff.mpr
  simp only [tasks, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, List.all_flatMap, Bool.and_eq_true, List.all_eq_true,
    keyTasks, evaluate, decide_eq_true_eq, replacement_iff, certified_iff,
    noQualifiedBehaviorLost_iff]
  constructor
  · rintro ⟨⟨ho, hn⟩, h⟩
    exact ⟨⟨ho, fun k hk => ⟨(h k hk).1, (h k hk).2.1⟩⟩,
      ⟨hn, fun k hk => ⟨(h k hk).2.2.1, (h k hk).2.2.2.1⟩⟩,
      fun k hk => (h k hk).2.2.2.2⟩
  · rintro ⟨⟨ho, hco⟩, ⟨hn, hcn⟩, hc⟩
    exact ⟨⟨ho, hn⟩, fun k hk =>
      ⟨(hco k hk).1, (hco k hk).2, (hcn k hk).1, (hcn k hk).2, hc k hk⟩⟩

/- Both successful and failed receipts carry a kernel-checked equality.
   A caller cannot supply an unrelated cached Boolean as evidence. -/
structure Evidence (s : Stamp Capability Outcome Key Context) where
  verdict : Bool
  correct : verdict = evaluate s

def proveFresh (s : Stamp Capability Outcome Key Context) : Evidence s :=
  ⟨evaluate s, rfl⟩

theorem Evidence.accepted {s : Stamp Capability Outcome Key Context}
    (e : Evidence s) (h : e.verdict = true) : Judgment s :=
  (evaluate_iff s).mp (e.correct.symm.trans h)

theorem Evidence.rejected {s : Stamp Capability Outcome Key Context}
    (e : Evidence s) (h : e.verdict = false) : ¬ Judgment s := by
  intro hj
  have ht := (evaluate_iff s).mpr hj
  have hf := e.correct.symm.trans h
  simp [ht] at hf

def Evidence.proof {s : Stamp Capability Outcome Key Context}
    (e : Evidence s) : Decidable (Judgment s) :=
  if h : e.verdict = true then isTrue (e.accepted h)
  else isFalse (fun hj => h (e.correct.trans ((evaluate_iff s).mpr hj)))

def reuse_transport {s t : Stamp Capability Outcome Key Context}
    (h : s = t) (e : Evidence s) : Evidence t := h ▸ e

theorem reuse_transport_verdict {s t : Stamp Capability Outcome Key Context}
    (h : s = t) (e : Evidence s) :
    (reuse_transport h e).verdict = e.verdict := by
  cases h
  rfl

structure Entry (Capability Outcome Key Context : Type)
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context] where
  stamp : Stamp Capability Outcome Key Context
  evidence : Evidence stamp

abbrev Cache (Capability Outcome Key Context : Type)
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context] :=
  List (Entry Capability Outcome Key Context)

def contains (cache : Cache Capability Outcome Key Context)
    (s : Stamp Capability Outcome Key Context) : Prop :=
  ∃ e ∈ cache, e.stamp = s

variable [DecidableEq Key]

def findEvidence (cache : Cache Capability Outcome Key Context)
    (s : Stamp Capability Outcome Key Context) : Option (Evidence s) :=
  match cache with
  | [] => none
  | e :: es =>
      if h : e.stamp = s then some (reuse_transport h e.evidence)
      else findEvidence es s

theorem findEvidence_present (cache : Cache Capability Outcome Key Context)
    (s : Stamp Capability Outcome Key Context) :
    (findEvidence cache s).isSome = true ↔ contains cache s := by
  induction cache with
  | nil => simp [findEvidence, contains]
  | cons e es ih =>
      by_cases h : e.stamp = s
      · simp [findEvidence, h, contains]
      · simp [findEvidence, h, contains] at ih ⊢
        exact ih

structure FetchResult (s : Stamp Capability Outcome Key Context) where
  evidence : Evidence s
  cache : Cache Capability Outcome Key Context
  evaluated : Nat
  reused : Nat

def fetch (cache : Cache Capability Outcome Key Context)
    (s : Stamp Capability Outcome Key Context) : FetchResult s :=
  match findEvidence cache s with
  | some e => ⟨e, cache, 0, 1⟩
  | none =>
      let e := proveFresh s
      ⟨e, cache ++ [⟨s, e⟩], 1, 0⟩

theorem fetch_counts (cache : Cache Capability Outcome Key Context)
    (s : Stamp Capability Outcome Key Context) :
    (fetch cache s).evaluated + (fetch cache s).reused = 1 := by
  unfold fetch
  split <;> rfl

theorem fetch_prefix (cache : Cache Capability Outcome Key Context)
    (s : Stamp Capability Outcome Key Context) :
    ∃ suffix, (fetch cache s).cache = cache ++ suffix := by
  unfold fetch
  split
  · exact ⟨[], (List.append_nil cache).symm⟩
  · exact ⟨[⟨s, proveFresh s⟩], rfl⟩

theorem fetch_growth (cache : Cache Capability Outcome Key Context)
    (s : Stamp Capability Outcome Key Context) :
    (fetch cache s).cache.length = cache.length + (fetch cache s).evaluated := by
  unfold fetch
  split <;> simp

theorem fetch_contains (cache : Cache Capability Outcome Key Context)
    (s : Stamp Capability Outcome Key Context) : contains (fetch cache s).cache s := by
  cases h : findEvidence cache s with
  | none =>
      refine ⟨⟨s, proveFresh s⟩, ?_, rfl⟩
      simp [fetch, h]
  | some e =>
      simpa [fetch, h] using (findEvidence_present cache s).mp (by simp [h])

theorem fetch_hit (cache : Cache Capability Outcome Key Context)
    (s : Stamp Capability Outcome Key Context) (h : contains cache s) :
    (fetch cache s).cache = cache ∧ (fetch cache s).evaluated = 0 ∧
      (fetch cache s).reused = 1 := by
  have hf := (findEvidence_present cache s).mpr h
  cases he : findEvidence cache s with
  | none => simp [he] at hf
  | some e => simp [fetch, he]

omit [DecidableEq Key] in
theorem contains_prefix {cache next : Cache Capability Outcome Key Context}
    {s : Stamp Capability Outcome Key Context}
    (hp : ∃ suffix, next = cache ++ suffix) (h : contains cache s) :
    contains next s := by
  obtain ⟨suffix, rfl⟩ := hp
  obtain ⟨e, he, hs⟩ := h
  exact ⟨e, List.mem_append_left _ he, hs⟩

structure Result (Capability Outcome Key Context : Type)
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context] where
  verdict : Bool
  cache : Cache Capability Outcome Key Context
  evaluated : Nat
  reused : Nat

def repair (cache : Cache Capability Outcome Key Context) :
    List (Stamp Capability Outcome Key Context) → Result Capability Outcome Key Context
  | [] => ⟨true, cache, 0, 0⟩
  | s :: ss =>
      let first := fetch cache s
      let rest := repair first.cache ss
      ⟨first.evidence.verdict && rest.verdict, rest.cache,
        first.evaluated + rest.evaluated, first.reused + rest.reused⟩

theorem repair_exact (cache : Cache Capability Outcome Key Context)
    (ss : List (Stamp Capability Outcome Key Context)) :
    (repair cache ss).verdict = ss.all evaluate := by
  induction ss generalizing cache with
  | nil => rfl
  | cons s ss ih =>
      simp only [repair, List.all_cons, ih, (fetch cache s).evidence.correct]

theorem repair_counts (cache : Cache Capability Outcome Key Context)
    (ss : List (Stamp Capability Outcome Key Context)) :
    (repair cache ss).evaluated + (repair cache ss).reused = ss.length := by
  induction ss generalizing cache with
  | nil => rfl
  | cons s ss ih =>
      have hf := fetch_counts cache s
      have hr := ih (fetch cache s).cache
      simp only [repair, List.length_cons]
      omega

theorem repair_prefix (cache : Cache Capability Outcome Key Context)
    (ss : List (Stamp Capability Outcome Key Context)) :
    ∃ suffix, (repair cache ss).cache = cache ++ suffix := by
  induction ss generalizing cache with
  | nil => exact ⟨[], (List.append_nil cache).symm⟩
  | cons s ss ih =>
      obtain ⟨first, hf⟩ := fetch_prefix cache s
      obtain ⟨rest, hr⟩ := ih (fetch cache s).cache
      refine ⟨first ++ rest, ?_⟩
      simp only [repair]
      rw [hr, hf, List.append_assoc]

theorem repair_growth (cache : Cache Capability Outcome Key Context)
    (ss : List (Stamp Capability Outcome Key Context)) :
    (repair cache ss).cache.length = cache.length + (repair cache ss).evaluated := by
  induction ss generalizing cache with
  | nil => rfl
  | cons s ss ih =>
      have hf := fetch_growth cache s
      have hr := ih (fetch cache s).cache
      simp only [repair]
      omega

theorem repair_coverage (cache : Cache Capability Outcome Key Context)
    (ss : List (Stamp Capability Outcome Key Context)) :
    ∀ s ∈ ss, contains (repair cache ss).cache s := by
  induction ss generalizing cache with
  | nil => simp
  | cons s ss ih =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact contains_prefix (repair_prefix (fetch cache t).cache ss)
          (fetch_contains cache t)
      · exact ih (fetch cache s).cache t ht

theorem repair_hit_only (cache : Cache Capability Outcome Key Context)
    (ss : List (Stamp Capability Outcome Key Context))
    (h : ∀ s ∈ ss, contains cache s) :
    (repair cache ss).cache = cache ∧ (repair cache ss).evaluated = 0 := by
  induction ss generalizing cache with
  | nil => exact ⟨rfl, rfl⟩
  | cons s ss ih =>
      have hf := fetch_hit cache s (h s (by simp))
      have hr := ih cache (fun t ht => h t (by simp [ht]))
      simpa only [repair, hf.1, hf.2.1, Nat.zero_add] using hr

theorem repair_repeat (cache : Cache Capability Outcome Key Context)
    (ss : List (Stamp Capability Outcome Key Context)) :
    (repair (repair cache ss).cache ss).cache = (repair cache ss).cache ∧
      (repair (repair cache ss).cache ss).evaluated = 0 :=
  repair_hit_only _ _ (repair_coverage cache ss)

def recertify (cache : Cache Capability Outcome Key Context)
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    Result Capability Outcome Key Context := repair cache (tasks q old new)

theorem verdict_eq (cache : Cache Capability Outcome Key Context)
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    (recertify cache q old new).verdict = replacement q old new :=
  (repair_exact cache (tasks q old new)).trans (tasks_exact q old new)

/- This proof is composed from the transported or newly produced leaf
   certificates by repair_exact. Full replacement is not an input premise. -/
theorem resultProof (cache : Cache Capability Outcome Key Context)
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    (recertify cache q old new).verdict = true ↔ replacement q old new = true := by
  rw [verdict_eq]

theorem recertify_prefix (cache : Cache Capability Outcome Key Context)
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    ∃ suffix, (recertify cache q old new).cache = cache ++ suffix :=
  repair_prefix cache (tasks q old new)

theorem recertify_repeat (cache : Cache Capability Outcome Key Context)
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    (recertify (recertify cache q old new).cache q old new).cache =
        (recertify cache q old new).cache ∧
      (recertify (recertify cache q old new).cache q old new).evaluated = 0 :=
  repair_repeat cache (tasks q old new)

theorem recertify_counts (cache : Cache Capability Outcome Key Context)
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    (recertify cache q old new).evaluated + (recertify cache q old new).reused =
      2 + 5 * q.keys.length :=
  (repair_counts cache (tasks q old new)).trans (tasks_length q old new)

theorem recertify_growth (cache : Cache Capability Outcome Key Context)
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    (recertify cache q old new).cache.length =
      cache.length + (recertify cache q old new).evaluated :=
  repair_growth cache (tasks q old new)

namespace Controls

def contract : Contract Nat Nat Nat Nat :=
  ⟨0, [0], fun _ => ⟨[0]⟩, fun _ => [0]⟩

def baseline : ScopedRelease Nat Nat Nat Nat :=
  ⟨0, fun _ => ⟨⟨[0]⟩, [0], (2, 2)⟩⟩

def candidate : ScopedRelease Nat Nat Nat Nat :=
  ⟨0, fun _ => ⟨⟨[0]⟩, [0], (1, 1)⟩⟩

def initial := recertify [] contract baseline candidate

theorem cold_checks_distinct_judgments :
    initial.verdict = true ∧ initial.evaluated = 4 ∧ initial.reused = 3 := by decide

theorem exact_replay_reuses_every_judgment :
    (recertify initial.cache contract baseline candidate).evaluated = 0 ∧
    (recertify initial.cache contract baseline candidate).reused = 7 := by decide

def cheaper : ScopedRelease Nat Nat Nat Nat :=
  ⟨0, fun _ => ⟨⟨[0]⟩, [0], (0, 1)⟩⟩

theorem cost_only_change_reproves_one_leaf :
    (recertify initial.cache contract baseline cheaper).evaluated = 1 ∧
    (recertify initial.cache contract baseline cheaper).reused = 6 ∧
    (recertify initial.cache contract baseline cheaper).verdict = true := by decide

def stricter : Contract Nat Nat Nat Nat :=
  { contract with prior := fun _ => ⟨[0, 1]⟩ }

theorem new_qualification_invalidates_old_proof :
    (recertify initial.cache stricter baseline candidate).evaluated = 1 ∧
    (recertify initial.cache stricter baseline candidate).verdict = false := by decide

theorem failed_evidence_is_reusable :
    let failed := recertify initial.cache stricter baseline candidate
    (recertify failed.cache stricter baseline candidate).verdict = false ∧
    (recertify failed.cache stricter baseline candidate).evaluated = 0 := by decide

def narrowed : Contract Nat Nat Nat Nat := { contract with allowed := fun _ => [] }

theorem envelope_change_invalidates_old_proof :
    (recertify initial.cache narrowed baseline candidate).evaluated = 1 ∧
    (recertify initial.cache narrowed baseline candidate).verdict = false := by decide

def lost : ScopedRelease Nat Nat Nat Nat :=
  { candidate with profile := fun _ => ⟨⟨[]⟩, [0], (1, 1)⟩ }

theorem offering_change_invalidates_old_proof :
    (recertify initial.cache contract baseline lost).evaluated = 1 ∧
    (recertify initial.cache contract baseline lost).verdict = false := by decide

def unsafeOutcome : ScopedRelease Nat Nat Nat Nat :=
  { candidate with profile := fun _ => ⟨⟨[0]⟩, [0, 1], (1, 1)⟩ }

theorem possible_outcome_change_invalidates_old_proof :
    (recertify initial.cache contract baseline unsafeOutcome).evaluated = 1 ∧
    (recertify initial.cache contract baseline unsafeOutcome).verdict = false := by decide

def cheaperBaseline : ScopedRelease Nat Nat Nat Nat :=
  { baseline with profile := fun _ => ⟨⟨[0]⟩, [0], (0, 0)⟩ }

theorem baseline_cost_change_invalidates_old_proof :
    (recertify initial.cache contract cheaperBaseline candidate).evaluated = 1 ∧
    (recertify initial.cache contract cheaperBaseline candidate).verdict = false := by decide

def expanded : Contract Nat Nat Nat Nat := { contract with keys := [0, 1] }

theorem added_key_cannot_reuse_another_keys_evidence :
    (recertify initial.cache expanded baseline candidate).evaluated = 3 ∧
    (recertify initial.cache expanded baseline candidate).reused = 9 := by decide

def moved : Contract Nat Nat Nat Nat := { contract with context := 1 }

theorem changed_context_cannot_reuse_stale_evidence :
    (recertify initial.cache moved baseline candidate).evaluated = 4 ∧
    (recertify initial.cache moved baseline candidate).verdict = false := by decide

theorem changed_candidate_context_cannot_reuse_stale_evidence :
    let changed := { candidate with context := 1 }
    (recertify initial.cache contract baseline changed).evaluated = 4 ∧
    (recertify initial.cache contract baseline changed).verdict = false := by decide

theorem changed_baseline_context_cannot_reuse_stale_evidence :
    let changed := { baseline with context := 1 }
    (recertify initial.cache contract changed candidate).evaluated = 4 ∧
    (recertify initial.cache contract changed candidate).verdict = false := by decide

/- Exact recertification describes the supplied contract. Authorizing a
   contract edit is a separate judgment; Evolution forbids this erasure. -/
theorem removed_key_changes_the_current_query :
    let failed := recertify initial.cache stricter baseline candidate
    let empty := { stricter with keys := [] }
    failed.verdict = false ∧
    (recertify failed.cache empty baseline candidate).verdict = true ∧
    (recertify failed.cache empty baseline candidate).evaluated = 0 := by decide

theorem restoring_inputs_recovers_archived_proofs :
    let changed := recertify initial.cache stricter baseline candidate
    (recertify changed.cache contract baseline candidate).evaluated = 0 ∧
    (recertify changed.cache contract baseline candidate).verdict = true := by decide

end Controls

end SoftwareDoesntRegress.Dynamic.Incremental
