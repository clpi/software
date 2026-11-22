import Audit.Definitional.Readings

/-!
# The conjunction that survives the counterexamples in `Readings`

Per symbol, keyed by id (not position, not a flat set):

* spec: every behavior is on that symbol's allow list, and every behavior the
  prior qualification holds for that symbol is still there (readings 2 and 6);
* cone: a symbol outside the change cone must be identical to the incumbent's
  and reuses its certificate; a symbol inside the cone must be separated, its
  upper time bound at or below the incumbent's lower bound (per-execution, the
  `weaklySeparated` form of reading 4);
* removal: an incumbent symbol may disappear only if nothing is qualified for it.

Premises that stay premises: the cone is complete over symbol, context, data,
configuration and deployment edges (`ContextCone`); observed behavior covers
real behavior (`Coverage.coverage`); the allow lists and prior qualification are
right; the measured context is the deployed one. One time axis keeps the toy
small; more axes are the same check per axis.
-/

namespace RegressAudit

structure Sym where
  id : Nat
  beh : List Nat
  tLo : Nat
  tHi : Nat
  deriving DecidableEq, Repr

structure Spec where
  allowed : Nat → List Nat
  prior : Nat → List Nat

def lookup (r : List Sym) (i : Nat) : Option Sym :=
  r.find? fun s => s.id == i

def behOk (s : Spec) (n : Sym) : Bool :=
  (s.prior n.id).all (fun b => decide (b ∈ n.beh)) &&
    n.beh.all (fun b => decide (b ∈ s.allowed n.id)) &&
    decide (n.tLo ≤ n.tHi)

def symAdmit (s : Spec) (inCone : Nat → Bool) (old : List Sym) (n : Sym) : Bool :=
  behOk s n &&
    match lookup old n.id with
    | none => true
    | some o => if inCone n.id then decide (n.tHi ≤ o.tLo) else decide (n = o)

def survives (s : Spec) (inCone : Nat → Bool) (old new : List Sym) : Bool :=
  old.all (fun o => (s.prior o.id).isEmpty || (lookup new o.id).isSome) &&
    new.all (symAdmit s inCone old)

/-! ## Controls: the reading-1..6 misjudgments, replayed -/

def spec0 : Spec where
  allowed _ := [ok, feature, legacy]
  prior i := if i = 0 then [ok] else []

def all : Nat → Bool := fun _ => true
def none' : Nat → Bool := fun _ => false

def base : List Sym := [⟨0, [ok], 10, 10⟩]

/-- Feature add at equal deterministic cost: accepted (reading 1 refused it). -/
theorem s_accepts_feature : survives spec0 all base [⟨0, [ok, feature], 10, 10⟩] = true := by
  decide

/-- Forbidden behavior: refused (readings 2 and the master gate accepted it). -/
theorem s_refuses_crash : survives spec0 all base [⟨0, [ok, crash], 10, 10⟩] = false := by
  decide

/-- Deleting the qualified behavior: refused (reading 1 accepted it). -/
theorem s_refuses_deletion : survives spec0 all base [⟨0, [], 10, 10⟩] = false := by decide

/-- Removing an unqualified crash, at half the cost: accepted (master gate refused it). -/
theorem s_accepts_bug_fix :
    survives spec0 all [⟨0, [ok, crash], 10, 10⟩] [⟨0, [ok], 5, 5⟩] = true := by decide

/-- Adding a symbol and reordering: accepted (master gate refused both). -/
theorem s_accepts_add_and_reorder :
    survives spec0 none' base [⟨7, [feature], 1, 1⟩, ⟨0, [ok], 10, 10⟩] = true := by
  decide

/-- Hundredfold slowdown inside the cone: refused (reading 3 accepted it). -/
theorem s_refuses_slowdown : survives spec0 all base [⟨0, [ok], 1000, 1000⟩] = false := by
  decide

/-- The repo's own endpoint case, `[10,20]` to `[8,18]`: refused, because an
execution at 18 can follow one at 10 (master gate accepted it). -/
theorem s_refuses_endpoint_overlap :
    survives spec0 all [⟨0, [ok], 10, 20⟩] [⟨0, [ok], 8, 18⟩] = false := by decide

/-- Moving `ok` from symbol 0 to symbol 1: refused (flat `ReleaseSafe` accepted it). -/
theorem s_refuses_move :
    survives spec0 none' [⟨0, [ok], 10, 10⟩, ⟨1, [], 1, 1⟩]
      [⟨0, [], 10, 10⟩, ⟨1, [ok], 1, 1⟩] = false := by decide

/-- Identical noisy rebuild outside the cone: accepted (bare separation refused it). -/
theorem s_accepts_untouched_noisy :
    survives spec0 none' [⟨0, [ok], 10, 11⟩] [⟨0, [ok], 10, 11⟩] = true := by decide

/-! ## What the conjunction still gets wrong: its price -/

/-- Deprecating a qualified behavior is refused until the spec itself changes. -/
theorem s_condemns_deprecation :
    survives { spec0 with prior := fun i => if i = 0 then [ok, legacy] else [] } all
      [⟨0, [ok, legacy], 10, 10⟩] [⟨0, [ok], 10, 10⟩] = false := by decide

/-- A real but noisy improvement inside the cone is refused: intervals overlap. -/
theorem s_condemns_overlapping_win :
    survives spec0 all [⟨0, [ok], 10, 20⟩] [⟨0, [ok], 9, 19⟩] = false := by decide

/-- A noisy, cost-neutral feature inside the cone is refused for the same reason. -/
theorem s_condemns_noisy_feature :
    survives spec0 all [⟨0, [ok], 10, 11⟩] [⟨0, [ok, feature], 10, 11⟩] = false := by decide

/-! ## Soundness of the conjunction -/

theorem lookup_some {r : List Sym} {i : Nat} {o : Sym} (h : lookup r i = some o) :
    o ∈ r ∧ o.id = i := by
  unfold lookup at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem lookup_isSome_of_mem {r : List Sym} {o : Sym} (h : o ∈ r) :
    (lookup r o.id).isSome = true := by
  unfold lookup
  rw [List.find?_isSome]
  exact ⟨o, h, by simp⟩

/-- Every symbol of an admitted release carries only allowed behaviors and every
behavior qualified for it. -/
theorem survives_spec {s : Spec} {c : Nat → Bool} {old new : List Sym}
    (h : survives s c old new = true) {n : Sym} (hn : n ∈ new) :
    (∀ b ∈ n.beh, b ∈ s.allowed n.id) ∧ (∀ b ∈ s.prior n.id, b ∈ n.beh) := by
  simp only [survives, Bool.and_eq_true, List.all_eq_true] at h
  have ha := h.2 n hn
  simp only [symAdmit, behOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ha
  exact ⟨ha.1.1.2, ha.1.1.1⟩

/-- No qualified symbol disappears. -/
theorem survives_keeps {s : Spec} {c : Nat → Bool} {old new : List Sym}
    (h : survives s c old new = true) {o : Sym} (ho : o ∈ old) (hq : s.prior o.id ≠ []) :
    ∃ n ∈ new, n.id = o.id := by
  simp only [survives, Bool.and_eq_true, List.all_eq_true] at h
  have hk := h.1 o ho
  simp only [Bool.or_eq_true] at hk
  rcases hk with he | hs
  · exact absurd (List.isEmpty_iff.mp he) hq
  · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨n, (lookup_some hn).1, (lookup_some hn).2⟩

/-- Inside the cone, every execution of the new symbol inside its bounds is no
slower than every execution of the incumbent symbol inside its bounds. -/
theorem survives_per_execution {s : Spec} {c : Nat → Bool} {old new : List Sym}
    (h : survives s c old new = true) {n o : Sym} (hn : n ∈ new)
    (hl : lookup old n.id = some o) (hc : c n.id = true)
    {x y : Nat} (hx : x ≤ n.tHi) (hy : o.tLo ≤ y) : x ≤ y := by
  simp only [survives, Bool.and_eq_true, List.all_eq_true] at h
  have ha := h.2 n hn
  simp only [symAdmit, Bool.and_eq_true, hl, hc, if_true, decide_eq_true_eq] at ha
  omega

/-- Outside the cone, the new symbol is the incumbent's, so its certificate carries over. -/
theorem survives_outside_identical {s : Spec} {c : Nat → Bool} {old new : List Sym}
    (h : survives s c old new = true) {n o : Sym} (hn : n ∈ new)
    (hl : lookup old n.id = some o) (hc : c n.id = false) : n = o := by
  simp only [survives, Bool.and_eq_true, List.all_eq_true] at h
  have ha := h.2 n hn
  simp only [symAdmit, Bool.and_eq_true, hl, hc, Bool.false_eq_true, if_false,
    decide_eq_true_eq] at ha
  exact ha.2

end RegressAudit
