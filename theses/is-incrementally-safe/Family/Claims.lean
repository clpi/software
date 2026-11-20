/-!
# Proposal entries S-08/S-09 (resolution) and S-10 (an unrecorded execution "occupies")

## S-09: "the highest-resolution representation", "collected once, known by derivation"

`Finer r q`: `q` can be computed from `r` without observing again. Proven:

* `finer_iff_kernel`: `q` is derivable from the record exactly when executions with the same
  record have the same `q`. This is the precise content of "known by derivation".
* `pair_finest`: the highest-resolution representation of a set of representations is their
  pairing: it is finer than each, and anything finer than each is finer than it.
* `finest_iff_injective`: a record derives every two-valued quantity exactly when it is
  injective, i.e. when it identifies the execution itself. So "highest resolution for any
  software on any kernel" holds only for a record that never merges two executions.
* `env_not_derivable`: if a quantity depends on something outside the record (the environment,
  as in the proposal's own V-E, where a second environment gives different numbers), it cannot
  be derived from the record. Recommendation: state S-09 as `finer_iff_kernel` with the record's
  scope named, and drop "any software on any kernel".

## S-10: "an unrecorded execution occupies on its next execution"

Proven: `occupies_same_key`: with an idempotent (set) account keyed by behavior class, recording
a later execution with the same key gives exactly the account the missed execution would have
given. Disproven as stated: `occupy_needs_same_key` (if the next execution falls in another
class, the missed class stays absent) and `occupy_fails_counting` (any counting account, such
as a sum of costs or a run count, still differs). In every case the missed execution itself is
never witnessed (`missed_stays_unwitnessed`). So the true statement is: the missed execution's
class is witnessed by the next execution of the same class, under an idempotent account.

Prior art: `finer_iff_kernel` and `pair_finest` are the standard kernel and product facts about
functions (any set-theory text); the idempotent-account fact is the join-semilattice property
behind state-based CRDTs (Shapiro et al. 2011). Nothing here is a new result; it is the precise
form of two proposal claims.
-/
namespace Family.Claims

open Classical

variable {W A B : Type}

/-- `q` is a function of `r`. -/
def Finer (r : W → A) (q : W → B) : Prop := ∃ f : A → B, ∀ w, q w = f (r w)

theorem finer_iff_kernel [Inhabited B] (r : W → A) (q : W → B) :
    Finer r q ↔ ∀ w w', r w = r w' → q w = q w' := by
  constructor
  · rintro ⟨f, hf⟩ w w' h
    rw [hf w, hf w', h]
  · intro h
    refine ⟨fun a => if hw : ∃ w, r w = a then q (choose hw) else default, fun w => ?_⟩
    have hw : ∃ w', r w' = r w := ⟨w, rfl⟩
    simp only [hw, dif_pos]
    exact h w (choose hw) (choose_spec hw).symm

theorem pair_finest {C : Type} (r1 : W → A) (r2 : W → B) :
    Finer (fun w => (r1 w, r2 w)) r1 ∧ Finer (fun w => (r1 w, r2 w)) r2 ∧
      ∀ r : W → C, Finer r r1 → Finer r r2 → Finer r (fun w => (r1 w, r2 w)) := by
  refine ⟨⟨Prod.fst, fun _ => rfl⟩, ⟨Prod.snd, fun _ => rfl⟩, ?_⟩
  rintro r ⟨f1, h1⟩ ⟨f2, h2⟩
  exact ⟨fun c => (f1 c, f2 c), fun w => by simp [h1 w, h2 w]⟩

theorem finest_iff_injective (r : W → A) :
    (∀ q : W → Bool, Finer r q) ↔ ∀ w w', r w = r w' → w = w' := by
  constructor
  · intro h w w' hr
    have := (finer_iff_kernel r (fun x => decide (x = w))).mp (h _) w w' hr
    simp at this
    exact this.symm
  · intro h q
    exact (finer_iff_kernel r q).mpr (fun w w' hr => by rw [h w w' hr])

/-- An execution with a record and an environment the record does not capture. -/
theorem env_not_derivable :
    ¬ Finer (fun x : Nat × Bool => x.1) (fun x => x.2) := by
  rintro ⟨f, hf⟩
  have h1 := hf (0, true)
  have h2 := hf (0, false)
  simp at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ## S-10 -/

variable {E K : Type}

/-- Idempotent account: which behavior classes have been witnessed. -/
def acct (key : E → K) (L : List E) (k : K) : Prop := ∃ e, e ∈ L ∧ key e = k

/-- A counting account: how many recorded executions fall in class `k`. -/
def count [DecidableEq K] (key : E → K) (L : List E) (k : K) : Nat :=
  (L.filter (fun e => key e = k)).length

theorem occupies_same_key (key : E → K) (L : List E) (e e' : E) (h : key e' = key e) :
    acct key (e' :: L) = acct key (e' :: e :: L) := by
  funext k
  apply propext
  constructor
  · rintro ⟨x, hx, hk⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨x, List.mem_cons_self, hk⟩
    · exact ⟨x, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx), hk⟩
  · rintro ⟨x, hx, hk⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨x, List.mem_cons_self, hk⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨e', List.mem_cons_self, h.trans hk⟩
    · exact ⟨x, List.mem_cons_of_mem _ hx, hk⟩

theorem missed_stays_unwitnessed (L : List E) (e e' : E) (hne : e ≠ e') (hL : e ∉ L) :
    e ∉ e' :: L := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · exact hne h
  · exact hL h

theorem occupy_needs_same_key :
    let key : Nat → Nat := id
    ¬ acct key [2] 1 ∧ acct key [2, 1] 1 := by
  refine ⟨?_, ⟨1, by simp, rfl⟩⟩
  rintro ⟨x, hx, hk⟩
  simp at hx
  subst hx
  simp at hk

theorem occupy_fails_counting :
    let key : Nat → Bool := fun _ => true
    count key [1] true ≠ count key [1, 0] true := by
  decide

end Family.Claims
