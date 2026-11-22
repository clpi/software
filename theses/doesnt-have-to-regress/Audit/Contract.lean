import SoftwareIsQuantifiable.Pareto

namespace SoftwareDoesntRegress.Audit

open SoftwareIsQuantifiable.Pareto

structure ScopedProfile (Capability Outcome : Type) where
  offered : BehaviorSubmission Capability
  possible : List Outcome
  cost : Point

structure ScopedRelease (Capability Outcome Key Context : Type) where
  context : Context
  profile : Key → ScopedProfile Capability Outcome

structure Contract (Capability Outcome Key Context : Type) where
  context : Context
  keys : List Key
  prior : Key → PriorQualification Capability
  allowed : Key → List Outcome

def permitted {Capability Outcome Key Context : Type} [DecidableEq Outcome]
    (q : Contract Capability Outcome Key Context)
    (r : ScopedRelease Capability Outcome Key Context) (k : Key) : Bool :=
  (r.profile k).possible.all fun o => decide (o ∈ q.allowed k)

def certified {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (q : Contract Capability Outcome Key Context)
    (r : ScopedRelease Capability Outcome Key Context) : Bool :=
  decide (r.context = q.context) && q.keys.all fun k =>
    noQualifiedBehaviorLost (q.prior k) (r.profile k).offered && permitted q r k

def compareCosts {Capability Outcome Key Context : Type}
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) : Bool :=
  q.keys.all fun k => decide (noWorse (new.profile k).cost (old.profile k).cost)

def replacement {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) : Bool :=
  certified q old && certified q new && compareCosts q old new

theorem permitted_iff {Capability Outcome Key Context : Type} [DecidableEq Outcome]
    (q : Contract Capability Outcome Key Context)
    (r : ScopedRelease Capability Outcome Key Context) (k : Key) :
    permitted q r k = true ↔ ∀ o ∈ (r.profile k).possible, o ∈ q.allowed k := by
  simp [permitted, List.all_eq_true]

theorem certified_iff {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (q : Contract Capability Outcome Key Context)
    (r : ScopedRelease Capability Outcome Key Context) :
    certified q r = true ↔ r.context = q.context ∧
      ∀ k ∈ q.keys,
        (∀ b ∈ (q.prior k).qualified, b ∈ (r.profile k).offered.offered) ∧
        (∀ o ∈ (r.profile k).possible, o ∈ q.allowed k) := by
  simp [certified, Bool.and_eq_true, List.all_eq_true,
    noQualifiedBehaviorLost_iff, permitted_iff]

theorem compareCosts_iff {Capability Outcome Key Context : Type}
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    compareCosts q old new = true ↔
      ∀ k ∈ q.keys, noWorse (new.profile k).cost (old.profile k).cost := by
  simp [compareCosts, List.all_eq_true]

theorem replacement_iff {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (q : Contract Capability Outcome Key Context)
    (old new : ScopedRelease Capability Outcome Key Context) :
    replacement q old new = true ↔
      certified q old = true ∧ certified q new = true ∧
      ∀ k ∈ q.keys, noWorse (new.profile k).cost (old.profile k).cost := by
  simp [replacement, Bool.and_eq_true, compareCosts_iff, and_assoc]

theorem replacement_uses_family_admission {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    {old new : ScopedRelease Capability Outcome Key Context}
    (h : replacement q old new = true) {k : Key} (hk : k ∈ q.keys) :
    acceptsRelease old.context new.context (q.prior k) (new.profile k).offered
      (old.profile k).cost (new.profile k).cost = true := by
  obtain ⟨ho, hn, hc⟩ := (replacement_iff q old new).mp h
  have ho := (certified_iff q old).mp ho
  have hn := (certified_iff q new).mp hn
  apply (acceptsRelease_iff _ _ _ _ _ _).mpr
  exact ⟨hn.1.trans ho.1.symm, (hn.2 k hk).1, hc k hk⟩

theorem replacement_preserves_requirements_and_envelope
    {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    {old new : ScopedRelease Capability Outcome Key Context}
    (h : replacement q old new = true) {k : Key} (hk : k ∈ q.keys) :
    (∀ b ∈ (q.prior k).qualified, b ∈ (new.profile k).offered.offered) ∧
    (∀ o ∈ (new.profile k).possible, o ∈ q.allowed k) ∧
    noWorse (new.profile k).cost (old.profile k).cost := by
  obtain ⟨_, hn, hc⟩ := (replacement_iff q old new).mp h
  have hn := ((certified_iff q new).mp hn).2 k hk
  exact ⟨hn.1, hn.2, hc k hk⟩

theorem replacement_refl {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    {r : ScopedRelease Capability Outcome Key Context} (h : certified q r = true) :
    replacement q r r = true := by
  apply (replacement_iff q r r).mpr
  exact ⟨h, h, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩

theorem replacement_trans {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    {a b c : ScopedRelease Capability Outcome Key Context}
    (hab : replacement q a b = true) (hbc : replacement q b c = true) :
    replacement q a c = true := by
  obtain ⟨ha, _, hab⟩ := (replacement_iff q a b).mp hab
  obtain ⟨_, hc, hbc⟩ := (replacement_iff q b c).mp hbc
  apply (replacement_iff q a c).mpr
  refine ⟨ha, hc, ?_⟩
  intro k hk
  exact ⟨Nat.le_trans (hbc k hk).1 (hab k hk).1,
    Nat.le_trans (hbc k hk).2 (hab k hk).2⟩

def ship {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (q : Contract Capability Outcome Key Context)
    (old candidate : ScopedRelease Capability Outcome Key Context) :=
  if replacement q old candidate then candidate else old

theorem ship_safe {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    {old : ScopedRelease Capability Outcome Key Context}
    (candidate : ScopedRelease Capability Outcome Key Context)
    (h : certified q old = true) : replacement q old (ship q old candidate) = true := by
  unfold ship
  split
  · assumption
  · exact replacement_refl h

theorem ship_witness {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (q : Contract Capability Outcome Key Context)
    (old candidate : ScopedRelease Capability Outcome Key Context) :
    ship q old candidate = candidate ∨ ship q old candidate = old := by
  unfold ship
  split <;> simp

def deploy {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (q : Contract Capability Outcome Key Context)
    (old candidate : ScopedRelease Capability Outcome Key Context) :
    Option (ScopedRelease Capability Outcome Key Context) :=
  if certified q old then some (ship q old candidate) else none

theorem deployed_safe {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    {old candidate result : ScopedRelease Capability Outcome Key Context}
    (h : deploy q old candidate = some result) :
    replacement q old result = true := by
  unfold deploy at h
  split at h
  · next hc =>
      have heq := Option.some.inj h
      subst result
      exact ship_safe candidate hc
  · contradiction

theorem invalid_baseline_blocks_deployment {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    {old : ScopedRelease Capability Outcome Key Context}
    (candidate : ScopedRelease Capability Outcome Key Context)
    (h : certified q old = false) : deploy q old candidate = none := by
  simp [deploy, h]

theorem baseline_valid_iff_deployment_exists {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (q : Contract Capability Outcome Key Context)
    (old candidate : ScopedRelease Capability Outcome Key Context) :
    certified q old = true ↔ ∃ result, deploy q old candidate = some result := by
  constructor
  · intro h
    exact ⟨ship q old candidate, by simp [deploy, h]⟩
  · rintro ⟨result, h⟩
    exact ((replacement_iff q old result).mp (deployed_safe h)).1

def shipped {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (q : Contract Capability Outcome Key Context)
    (stream : Nat → ScopedRelease Capability Outcome Key Context) :
    Nat → ScopedRelease Capability Outcome Key Context
  | 0 => stream 0
  | n + 1 => ship q (shipped q stream n) (stream (n + 1))

theorem shipped_certified {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    (stream : Nat → ScopedRelease Capability Outcome Key Context)
    (h : certified q (stream 0) = true) (n : Nat) :
    certified q (shipped q stream n) = true := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact ((replacement_iff q _ _).mp (ship_safe (stream (n + 1)) ih)).2.1

theorem shipped_adjacent {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    (stream : Nat → ScopedRelease Capability Outcome Key Context)
    (h : certified q (stream 0) = true) (n : Nat) :
    replacement q (shipped q stream n) (shipped q stream (n + 1)) = true :=
  ship_safe (stream (n + 1)) (shipped_certified stream h n)

theorem shipped_add {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    (stream : Nat → ScopedRelease Capability Outcome Key Context)
    (h : certified q (stream 0) = true) (m d : Nat) :
    replacement q (shipped q stream m) (shipped q stream (m + d)) = true := by
  induction d with
  | zero => exact replacement_refl (shipped_certified stream h m)
  | succ d ih =>
    exact replacement_trans ih (shipped_adjacent stream h (m + d))

theorem shipped_chain {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    (stream : Nat → ScopedRelease Capability Outcome Key Context)
    (h : certified q (stream 0) = true) {m n : Nat} (hmn : m ≤ n) :
    replacement q (shipped q stream m) (shipped q stream n) = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact shipped_add stream h m d

theorem no_strict_reverse_dominance {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context}
    {old new : ScopedRelease Capability Outcome Key Context}
    (h : replacement q old new = true) {k : Key} (hk : k ∈ q.keys) :
    ¬ dominates (old.profile k).cost (new.profile k).cost := by
  have hc := ((replacement_iff q old new).mp h).2.2 k hk
  unfold noWorse at hc
  intro hd
  unfold dominates at hd
  omega

def recordPromises {Capability Outcome Key Context : Type}
    (q : Contract Capability Outcome Key Context) (extra : Key → List Capability) :
    Contract Capability Outcome Key Context :=
  { q with prior := fun k => { qualified := (q.prior k).qualified ++ extra k } }

theorem recorded_promises_preserved {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    {q : Contract Capability Outcome Key Context} {extra : Key → List Capability}
    {r : ScopedRelease Capability Outcome Key Context}
    (h : certified (recordPromises q extra) r = true) {k : Key} (hk : k ∈ q.keys) :
    (∀ b ∈ (q.prior k).qualified, b ∈ (r.profile k).offered.offered) ∧
    (∀ b ∈ extra k, b ∈ (r.profile k).offered.offered) := by
  have hp := ((certified_iff (recordPromises q extra) r).mp h).2 k hk
  constructor
  · intro b hb
    exact hp.1 b (List.mem_append.mpr (Or.inl hb))
  · intro b hb
    exact hp.1 b (List.mem_append.mpr (Or.inr hb))

theorem recordPromises_certified_iff {Capability Outcome Key Context : Type}
    [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Context]
    (q : Contract Capability Outcome Key Context) (extra : Key → List Capability)
    (r : ScopedRelease Capability Outcome Key Context) :
    certified (recordPromises q extra) r = true ↔
      certified q r = true ∧
      ∀ k ∈ q.keys, ∀ b ∈ extra k, b ∈ (r.profile k).offered.offered := by
  rw [certified_iff, certified_iff]
  constructor
  · intro h
    refine ⟨⟨h.1, ?_⟩, ?_⟩
    · intro k hk
      exact ⟨fun b hb => (h.2 k hk).1 b (List.mem_append.mpr (Or.inl hb)), (h.2 k hk).2⟩
    · intro k hk b hb
      exact (h.2 k hk).1 b (List.mem_append.mpr (Or.inr hb))
  · intro h
    refine ⟨h.1.1, ?_⟩
    intro k hk
    refine ⟨?_, (h.1.2 k hk).2⟩
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact (h.1.2 k hk).1 b hb
    · exact h.2 k hk b hb

end SoftwareDoesntRegress.Audit
