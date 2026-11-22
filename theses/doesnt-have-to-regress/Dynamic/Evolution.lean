import Audit.Contract

namespace SoftwareDoesntRegress.Dynamic.Evolution

open SoftwareDoesntRegress.Audit

variable {Capability Outcome Key Context : Type}
  [DecidableEq Capability] [DecidableEq Outcome] [DecidableEq Key] [DecidableEq Context]

/-- Existing commitments cannot disappear during an ordinary contract evolution.
New keys establish their first cost baseline at the admitting release. -/
def strengthens (old next : Contract Capability Outcome Key Context) : Bool :=
  decide (next.context = old.context) && old.keys.all fun k =>
    decide (k ∈ next.keys) &&
    (old.prior k).qualified.all (fun b => decide (b ∈ (next.prior k).qualified)) &&
    (next.allowed k).all (fun o => decide (o ∈ old.allowed k))

theorem strengthens_iff (old next : Contract Capability Outcome Key Context) :
    strengthens old next = true ↔ next.context = old.context ∧
      ∀ k ∈ old.keys, k ∈ next.keys ∧
        (∀ b ∈ (old.prior k).qualified, b ∈ (next.prior k).qualified) ∧
        (∀ o ∈ next.allowed k, o ∈ old.allowed k) := by
  simp [strengthens, Bool.and_eq_true, List.all_eq_true, and_assoc]

theorem strengthens_refl (q : Contract Capability Outcome Key Context) :
    strengthens q q = true := by
  apply (strengthens_iff q q).mpr
  exact ⟨rfl, fun _ hk => ⟨hk, fun _ hb => hb, fun _ ho => ho⟩⟩

theorem strengthens_trans {a b c : Contract Capability Outcome Key Context}
    (hab : strengthens a b = true) (hbc : strengthens b c = true) :
    strengthens a c = true := by
  obtain ⟨habctx, hab⟩ := (strengthens_iff a b).mp hab
  obtain ⟨hbcctx, hbc⟩ := (strengthens_iff b c).mp hbc
  apply (strengthens_iff a c).mpr
  refine ⟨hbcctx.trans habctx, ?_⟩
  intro k hk
  have hx := hab k hk
  have hy := hbc k hx.1
  exact ⟨hy.1, fun b hb => hy.2.1 b (hx.2.1 b hb),
    fun o ho => hx.2.2 o (hy.2.2 o ho)⟩

theorem stronger_certified {old next : Contract Capability Outcome Key Context}
    {r : ScopedRelease Capability Outcome Key Context}
    (hs : strengthens old next = true) (hc : certified next r = true) :
    certified old r = true := by
  obtain ⟨hctx, hs⟩ := (strengthens_iff old next).mp hs
  obtain ⟨hrctx, hc⟩ := (certified_iff next r).mp hc
  apply (certified_iff old r).mpr
  refine ⟨hrctx.trans hctx, ?_⟩
  intro k hk
  have hx := hs k hk
  have hy := hc k hx.1
  exact ⟨fun b hb => hy.1 b (hx.2.1 b hb), fun o ho => hx.2.2 o (hy.2 o ho)⟩

theorem stronger_replacement {old next : Contract Capability Outcome Key Context}
    {a b : ScopedRelease Capability Outcome Key Context}
    (hs : strengthens old next = true) (hr : replacement next a b = true) :
    replacement old a b = true := by
  obtain ⟨ha, hb, hcost⟩ := (replacement_iff next a b).mp hr
  apply (replacement_iff old a b).mpr
  exact ⟨stronger_certified hs ha, stronger_certified hs hb,
    fun k hk => hcost k (((strengthens_iff old next).mp hs).2 k hk).1⟩

theorem recordPromises_strengthens (q : Contract Capability Outcome Key Context)
    (extra : Key → List Capability) : strengthens q (recordPromises q extra) = true := by
  apply (strengthens_iff q (recordPromises q extra)).mpr
  exact ⟨rfl, fun _ hk => ⟨hk,
    fun _ hb => List.mem_append.mpr (Or.inl hb), fun _ ho => ho⟩⟩

structure Frame (Capability Outcome Key Context : Type) where
  contract : Contract Capability Outcome Key Context
  release : ScopedRelease Capability Outcome Key Context

/-- Admit the release under the old obligations, then establish the new ones.
Requiring the old release to satisfy newly introduced promises would reject
the very feature addition that creates them. -/
def admissible (old next : Frame Capability Outcome Key Context) : Bool :=
  replacement old.contract old.release next.release &&
  strengthens old.contract next.contract && certified next.contract next.release

theorem admissible_iff (old next : Frame Capability Outcome Key Context) :
    admissible old next = true ↔
      replacement old.contract old.release next.release = true ∧
      strengthens old.contract next.contract = true ∧
      certified next.contract next.release = true := by
  simp [admissible, Bool.and_eq_true, and_assoc]

theorem admissible_refl {frame : Frame Capability Outcome Key Context}
    (hc : certified frame.contract frame.release = true) :
    admissible frame frame = true :=
  (admissible_iff frame frame).mpr ⟨replacement_refl hc, strengthens_refl _, hc⟩

theorem admissible_trans {a b c : Frame Capability Outcome Key Context}
    (hab : admissible a b = true) (hbc : admissible b c = true) :
    admissible a c = true := by
  obtain ⟨hab, hsab, _⟩ := (admissible_iff a b).mp hab
  obtain ⟨hbc, hsbc, hc⟩ := (admissible_iff b c).mp hbc
  exact (admissible_iff a c).mpr
    ⟨replacement_trans hab (stronger_replacement hsab hbc),
      strengthens_trans hsab hsbc, hc⟩

def commit (old next : Frame Capability Outcome Key Context) :
    Option (Frame Capability Outcome Key Context) :=
  if admissible old next then some next else none

theorem commit_exact {old next result : Frame Capability Outcome Key Context} :
    commit old next = some result ↔ admissible old next = true ∧ result = next := by
  by_cases h : admissible old next = true
  · simp only [commit, h, if_true, Option.some.injEq, true_and]
    exact eq_comm
  · simp [commit, h]

def step (old candidate : Frame Capability Outcome Key Context) :
    Frame Capability Outcome Key Context :=
  if admissible old candidate then candidate else old

theorem step_safe {old : Frame Capability Outcome Key Context}
    (candidate : Frame Capability Outcome Key Context)
    (hc : certified old.contract old.release = true) :
    admissible old (step old candidate) = true := by
  unfold step
  split
  · assumption
  · exact admissible_refl hc

def follow (stream : Nat → Frame Capability Outcome Key Context) :
    Nat → Frame Capability Outcome Key Context
  | 0 => stream 0
  | n + 1 => step (follow stream n) (stream (n + 1))

theorem follow_certified (stream : Nat → Frame Capability Outcome Key Context)
    (h0 : certified (stream 0).contract (stream 0).release = true) (n : Nat) :
    certified (follow stream n).contract (follow stream n).release = true := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    exact ((admissible_iff _ _).mp (step_safe (stream (n + 1)) ih)).2.2

theorem follow_adjacent (stream : Nat → Frame Capability Outcome Key Context)
    (h0 : certified (stream 0).contract (stream 0).release = true) (n : Nat) :
    admissible (follow stream n) (follow stream (n + 1)) = true :=
  step_safe (stream (n + 1)) (follow_certified stream h0 n)

theorem follow_add (stream : Nat → Frame Capability Outcome Key Context)
    (h0 : certified (stream 0).contract (stream 0).release = true) (m d : Nat) :
    admissible (follow stream m) (follow stream (m + d)) = true := by
  induction d with
  | zero => exact admissible_refl (follow_certified stream h0 m)
  | succ d ih => exact admissible_trans ih (follow_adjacent stream h0 (m + d))

/-- Earlier promises, envelopes, protected keys and costs survive any number
of checked contract changes within a comparison context. -/
theorem historical_contracts_preserved (stream : Nat → Frame Capability Outcome Key Context)
    (h0 : certified (stream 0).contract (stream 0).release = true)
    {m n : Nat} (hmn : m ≤ n) :
    admissible (follow stream m) (follow stream n) = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact follow_add stream h0 m d

namespace Controls

def base : Contract Nat Nat Nat Nat :=
  { context := 0, keys := [0], prior := fun _ => { qualified := [0] },
    allowed := fun _ => [0] }

def promised : Contract Nat Nat Nat Nat := recordPromises base (fun _ => [1])

def before : ScopedRelease Nat Nat Nat Nat :=
  { context := 0, profile := fun _ =>
    { offered := { offered := [0] }, possible := [0], cost := (2, 2) } }

def after : ScopedRelease Nat Nat Nat Nat :=
  { context := 0, profile := fun _ =>
    { offered := { offered := [0, 1] }, possible := [0], cost := (1, 2) } }

theorem feature_can_create_its_own_promise :
    admissible ⟨base, before⟩ ⟨promised, after⟩ = true := by decide

theorem old_release_need_not_satisfy_future_promise :
    certified promised before = false := by decide

theorem promise_erasure_refused : strengthens promised base = false := by decide

theorem scope_erasure_refused : strengthens base { base with keys := [] } = false := by decide

theorem envelope_weakening_refused :
    strengthens base { base with allowed := fun _ => [0, 1] } = false := by decide

theorem context_switch_is_not_ordinary_evolution :
    strengthens base { base with context := 1 } = false := by decide

end Controls
end SoftwareDoesntRegress.Dynamic.Evolution
