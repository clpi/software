/-
  The synthesis across the software family, assembled
  constructively in this development.

  Three kinds of imported content, kept distinct:

  - Mirrored and discharged: statements copied verbatim
    from a sibling development at its pin, over definitions
    identical to the source's, and proved again here. The
    only claim resting on reading is that the mirror is
    faithful; the statements and pins are named in the
    specification's synthesis section.
  - Restated hypotheses: results whose source vocabulary
    this development does not mirror, stated here in this
    development's vocabulary and carried as explicit
    hypotheses of the joined theorem, so the joined
    statement shows its full dependency list.
  - Named premises: propositions the source developments
    themselves label as premises. They are carried in the
    joined theorem's antecedent, because they bind where
    the composed method may be applied to a real system;
    no conjunct's proof below uses them, and the
    specification says so.
-/

import Core

namespace Synthesis

open Persistence

/-! ## The losses import, mirrored and discharged

    Source: software-losses-are-compositional at the pin
    named in the specification. The definitions below are
    the source's, verbatim; every theorem of the source's
    core is proved here from them. -/

/-- The derived total of an additive record: the plain
    sum of its parts. -/
def derive (r : List Nat) : Nat := r.sum

/-- The projection of a record under one axis map: map,
    then sum. -/
def project (f : Nat → Nat) (r : List Nat) : Nat :=
  (r.map f).sum

/-- The gap of a record against a requirement under one
    axis: what the projection falls short of, truncated
    at zero. -/
def gap (f : Nat → Nat) (req : Nat) (r : List Nat) : Nat :=
  req - project f r

/-- A record is free on one axis when its projection
    meets the requirement. -/
def free (f : Nat → Nat) (req : Nat) (r : List Nat) : Prop :=
  req ≤ project f r

/-- A loss contract: the capability list and the design
    list whose grid is the candidate space. -/
structure LContract where
  caps : List Nat
  designs : List Nat

/-- The grid of a capability list against a design list:
    every pair, capability-major. -/
def grid : List Nat → List Nat → List (Nat × Nat)
  | [], _ => []
  | v :: rest, orders => orders.map (fun o => (v, o)) ++ grid rest orders

/-- The candidate space of a loss contract. -/
def space (c : LContract) : List (Nat × Nat) := grid c.caps c.designs

/-- The boolean check of freedom on one axis. -/
def check (f : Nat → Nat) (req : Nat) (r : List Nat) : Bool :=
  decide (req ≤ project f r)

/-- The boolean check of freedom on every axis of a
    list. -/
def allcheck (axes : List (Nat → Nat)) (req : Nat) (r : List Nat) :
    Bool :=
  axes.all (fun f => check f req r)

theorem sumapp (a b : List Nat) :
    (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp only [List.nil_append, List.sum_nil, Nat.zero_add]
  | cons x xs ih =>
    simp only [List.cons_append, List.sum_cons, ih, Nat.add_assoc]

theorem additive (a b : List Nat) :
    derive (a ++ b) = derive a + derive b :=
  sumapp a b

theorem projected (f : Nat → Nat) (a b : List Nat) :
    project f (a ++ b) = project f a + project f b := by
  simp only [project, List.map_append, sumapp]

theorem split (f : Nat → Nat) (a inter b : List Nat) :
    project f (a ++ inter ++ b)
      = project f a + project f inter + project f b := by
  rw [projected f (a ++ inter) b, projected f a inter]

theorem gapfree (f : Nat → Nat) (req : Nat) (r : List Nat) :
    gap f req r = 0 ↔ free f req r :=
  Nat.sub_eq_zero_iff_le

theorem composed (f : Nat → Nat) (s1 s2 : Nat) (a b : List Nat)
    (h1 : free f s1 a) (h2 : free f s2 b) :
    free f (s1 + s2) (a ++ b) := by
  show s1 + s2 ≤ project f (a ++ b)
  rw [projected]
  exact Nat.add_le_add h1 h2

theorem wholefree (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat)
    (h1 : free f s1 a) (hi : free f si inter)
    (h2 : free f s2 b) :
    free f (s1 + si + s2) (a ++ inter ++ b) := by
  show s1 + si + s2 ≤ project f (a ++ inter ++ b)
  rw [split]
  exact Nat.add_le_add (Nat.add_le_add h1 hi) h2

theorem leterm (a b : Nat) : a ≤ (a - b) + b := by
  rcases Nat.le_total b a with h | h
  · rw [Nat.sub_add_cancel h]
    exact Nat.le_refl a
  · have e : a - b = 0 := Nat.sub_eq_zero_of_le h
    rw [e, Nat.zero_add]
    exact h

theorem subadd3 (x1 x2 x3 y1 y2 y3 : Nat) :
    (x1 + x2 + x3) - (y1 + y2 + y3)
      ≤ (x1 - y1) + (x2 - y2) + (x3 - y3) := by
  rw [Nat.sub_le_iff_le_add]
  calc x1 + x2 + x3
      ≤ ((x1 - y1) + y1) + ((x2 - y2) + y2) + ((x3 - y3) + y3) :=
        Nat.add_le_add
          (Nat.add_le_add (leterm x1 y1) (leterm x2 y2))
          (leterm x3 y3)
    _ = ((x1 - y1) + (x2 - y2) + (x3 - y3)) + (y1 + y2 + y3) := by
        ac_rfl

theorem compound (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat) :
    gap f (s1 + si + s2) (a ++ inter ++ b)
      ≤ gap f s1 a + gap f si inter + gap f s2 b := by
  show (s1 + si + s2) - project f (a ++ inter ++ b) ≤ _
  rw [split]
  exact subadd3 _ _ _ _ _ _

theorem localizes (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat)
    (h : project f (a ++ inter ++ b) < s1 + si + s2) :
    project f a < s1 ∨ project f inter < si
      ∨ project f b < s2 := by
  rw [split] at h
  rcases Nat.lt_or_ge (project f a) s1 with h1 | h1
  · exact Or.inl h1
  · rcases Nat.lt_or_ge (project f inter) si with h2 | h2
    · exact Or.inr (Or.inl h2)
    · rcases Nat.lt_or_ge (project f b) s2 with h3 | h3
      · exact Or.inr (Or.inr h3)
      · exfalso
        have hsum : s1 + si + s2
            ≤ project f a + project f inter + project f b :=
          Nat.add_le_add (Nat.add_le_add h1 h2) h3
        exact Nat.not_lt_of_ge hsum h

theorem sound (f : Nat → Nat) (req : Nat) (r : List Nat)
    (h : check f req r = true) : free f req r := by
  have h2 : decide (req ≤ project f r) = true := h
  have h3 : req ≤ project f r := of_decide_eq_true h2
  exact h3

theorem allsound (axes : List (Nat → Nat)) (req : Nat)
    (r : List Nat) (h : allcheck axes req r = true) :
    ∀ f ∈ axes, free f req r := by
  intro f hf
  exact sound f req r ((List.all_eq_true.mp h) f hf)

theorem gridlength (vs os : List Nat) :
    (grid vs os).length = vs.length * os.length := by
  induction vs with
  | nil => simp only [grid, List.length_nil, Nat.zero_mul]
  | cons v rest ih =>
    have e : grid (v :: rest) os
        = os.map (fun o => (v, o)) ++ grid rest os := rfl
    rw [e, List.length_append, List.length_map, ih,
      List.length_cons]
    calc os.length + rest.length * os.length
        = rest.length * os.length + os.length := Nat.add_comm _ _
      _ = (rest.length + 1) * os.length := by
          rw [Nat.add_mul, Nat.one_mul]

theorem spacefinite (c : LContract) :
    (space c).length = c.caps.length * c.designs.length :=
  gridlength c.caps c.designs

theorem gapzero (axes : List (Nat → Nat)) (req : Nat)
    (r : List Nat) (h : allcheck axes req r = true)
    (f : Nat → Nat) (hf : f ∈ axes) : gap f req r = 0 :=
  (gapfree f req r).mpr (allsound axes req r h f hf)

/-! ## The profiling import: the baseline mirror, and
    least cost over a finite list

    Source: software-profiling-is-synthesizable at the pin
    named in the specification. The derived quantity of a
    measurement depends only on the overlap and witness
    terms; the baseline is carried by the measured form
    and never enters the value. That is the source's
    baseline theorem, over definitions identical to the
    source's, and it is proved here by computation. The
    source's solved-configuration content — a least-cost
    member exists in every nonempty finite configuration
    list — is the least-cost lemma below, in this
    development's vocabulary. -/

/-- The derived quantity of a measurement: overlap plus
    witness terms. -/
def pderived (overlap witness : Nat) : Nat := overlap + witness

/- The measured quantity: the derived quantity, with
   the baseline term carried and unused — the carrying
   is the content of the baseline theorem, so the linter
   note for the unused argument is silenced for this one
   definition, as in the source. -/
set_option linter.unusedVariables false in
def pmeasured (overlap witness baseline : Nat) : Nat :=
  pderived overlap witness

theorem profbaseline (o w b1 b2 : Nat) :
    pmeasured o w b1 = pmeasured o w b2 := rfl

theorem leastcost (c : Nat → Nat) :
    ∀ (l : List Nat), l ≠ [] →
      ∃ x ∈ l, ∀ y ∈ l, c x ≤ c y := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _
    cases l with
    | nil =>
      exact ⟨a, List.mem_cons.mpr (Or.inl rfl), fun y hy => by
        have e : y = a := List.mem_singleton.mp hy
        subst e
        exact Nat.le_refl _⟩
    | cons b l' =>
      obtain ⟨x, hx, hmin⟩ := ih (by simp)
      rcases Nat.le_total (c a) (c x) with hle | hle
      · refine ⟨a, List.mem_cons.mpr (Or.inl rfl), fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_refl _
        · exact Nat.le_trans hle (hmin y hy)
      · refine ⟨x, List.mem_cons_of_mem a hx, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hle
        · exact hmin y hy

/-! ## The traceability import, mirrored on the node
    projection and discharged

    Source: software-is-more-traceable-than-you-think at
    the pin named in the specification. The source's fold
    is a two-sorted graph fold; what the joined method
    consumes is its node content: a node is in the fold
    exactly when some retained event contributes it, and
    retraction commutes with the fold. Mirrored here with
    the fold as the flat map of a contribution function,
    both statements are proved. -/

/-- The node fold of an event list under a contribution
    function. -/
def tfold (c : Nat → List Nat) (es : List Nat) : List Nat :=
  es.flatMap c

theorem tmem (c : Nat → List Nat) (es : List Nat) (n : Nat) :
    n ∈ tfold c es ↔ ∃ e ∈ es, n ∈ c e :=
  List.mem_flatMap

theorem tretract (c : Nat → List Nat) (es : List Nat)
    (keep : Nat → Bool) (n : Nat) :
    n ∈ tfold c (es.filter keep)
      ↔ ∃ e ∈ es, keep e = true ∧ n ∈ c e := by
  rw [tmem]
  constructor
  · rintro ⟨e, he, hn⟩
    rw [List.mem_filter] at he
    exact ⟨e, he.1, he.2, hn⟩
  · rintro ⟨e, he, hk, hn⟩
    exact ⟨e, List.mem_filter.mpr ⟨he, hk⟩, hn⟩

/-! ## The compilers-lose-info discipline

    The source's no-recovery result, carried as an
    explicit hypothesis of this one lemma: an artifact map
    that identifies two quotient-distinct programs admits
    no recovery of the quotient. The joined method
    therefore claims recovery only for derivation-carrying
    representations, whose soundness is the certificate
    theorem of the core development. The hypothesis's
    source, pin, and original form are recorded in the
    specification's synthesis section. -/

theorem onlycarrying (G A Q : Type) (qual : G → Q)
    (h_norecov : ∀ (f : G → A) (g1 g2 : G),
      qual g1 ≠ qual g2 → f g1 = f g2 →
      ¬ ∃ r : A → Q, ∀ g, r (f g) = qual g)
    (f : G → A) (g1 g2 : G)
    (h1 : qual g1 ≠ qual g2) (h2 : f g1 = f g2) :
    ¬ ∃ r : A → Q, ∀ g, r (f g) = qual g :=
  h_norecov f g1 g2 h1 h2

/-! ## The joined theorem

    One constructive method for an arbitrary system,
    assembled from the parts. Every hypothesis the
    assembly rests on is an explicit argument, in three
    groups: the family's five named premises (the first
    group, carried in one antecedent); the restated
    results of the siblings (bounds soundness and
    attainment, incremental-equals-full for measurement
    and for re-checking, admission composition under its
    interaction side condition, safety-checker soundness,
    frontier completeness, and quotient recovery by
    carrying); and the method's own inputs (the record
    and its axis check, the datum and its contract, the
    recorded edges and store, the versions, the workload
    list, and the admission facts).

    Read the conjuncts in order: the record is checked
    free on every axis; any computation the certificate
    checker accepts is genuinely redundant, and adjoining
    its conclusion changes the derivable set not at all;
    a minimum representation of the datum exists in the
    finite candidate space; the frontier over that space
    is complete; the minimality verdict is independently
    checkable; every readable version survives any growth
    of the store; measurement is baseline-free; the
    incremental accounting equals the full accounting,
    for measurement and for re-checking alike; the
    derived bounds on the workload list are attained by
    members of it; admission composes over the record's
    segments under the interaction side condition; the
    safety checker's acceptance implies safety; carrying
    representations recover the qualified quotient; and
    the candidate count is the computed power.

    The premise antecedent binds where the method may be
    applied to a real system — the recorded edges must be
    faithful, the coverage of the qualification must be
    real, the specification authority must hold, witness
    states must be certified, and the general
    join-semilattice claim must be granted where the
    wider program uses it. The conjuncts' proofs do not
    use it; the linter silence on the next line covers
    exactly that antecedent, and no other declaration. -/

set_option linter.unusedVariables false in
theorem joined
    (Coverage SpecAuthority JoinSemi WitnessFaith
      RecordFaith : Prop)
    (hprem : Coverage ∧ SpecAuthority ∧ JoinSemi
      ∧ WitnessFaith ∧ RecordFaith)
    (bmin bmax : List Nat → Nat)
    (h_bsound : ∀ (ws : List Nat) (v : Nat),
      v ∈ ws → bmin ws ≤ v ∧ v ≤ bmax ws)
    (h_battained : ∀ (ws : List Nat), ws ≠ [] →
      bmin ws ∈ ws ∧ bmax ws ∈ ws)
    (full : List Nat → Nat)
    (incr : List Nat → List Nat → Nat)
    (h_incr : ∀ (base add : List Nat),
      incr base add = full (base ++ add))
    (recheck sfull : List Nat → Bool)
    (h_recheck : ∀ r, recheck r = sfull r)
    (IC : Prop) (Adm : List Nat → Prop)
    (h_adm : IC → ∀ (a b : List Nat),
      Adm a → Adm b → Adm (a ++ b))
    (Safe : List Nat → Prop) (scheck : List Nat → Bool)
    (h_ssound : ∀ r, scheck r = true → Safe r)
    (h_frontier :
      ∀ (axes : List (Nat → Nat → Nat)) (d : List Nat)
        (cands : List (List Nat)) (r : List Nat),
        r ∈ cands →
        Minimal axes d cands r
          ∨ ∃ m ∈ cands, Minimal axes d cands m
              ∧ Dominates axes d m r)
    (G A Q : Type) (carry : G → A) (recover : A → Q)
    (qual : G → Q)
    (h_carry : ∀ g, recover (carry g) = qual g)
    (hic : IC)
    (axes : List (Nat → Nat)) (req : Nat)
    (ra ri rb : List Nat)
    (hcheck : allcheck axes req (ra ++ ri ++ rb) = true)
    (paxes : List (Nat → Nat → Nat)) (datum : List Nat)
    (ch : List Nat)
    (hne : reps ch datum.length ≠ [])
    (edges : List (List Nat × Nat)) (stored : List Nat)
    (versions : List (List Nat))
    (ws : List Nat) (hws : ws ≠ [])
    (rec add : List Nat)
    (hadm : Adm ra ∧ Adm ri ∧ Adm rb) :
    (∀ f ∈ axes, free f req (ra ++ ri ++ rb))
    ∧ (∀ (cert : List (List Nat × Nat)) (t : Nat),
        checkCert edges stored t cert = true →
        Deriv edges stored t
          ∧ ∀ x, Deriv edges (t :: stored) x
              ↔ Deriv edges stored x)
    ∧ (∃ r ∈ reps ch datum.length,
        Minimal paxes datum (reps ch datum.length) r)
    ∧ (∀ r ∈ reps ch datum.length,
        Minimal paxes datum (reps ch datum.length) r
          ∨ ∃ m ∈ reps ch datum.length,
              Minimal paxes datum (reps ch datum.length) m
                ∧ Dominates paxes datum m r)
    ∧ (∀ r, minimalB paxes datum (reps ch datum.length) r
        = true →
        Minimal paxes datum (reps ch datum.length) r)
    ∧ (∀ v ∈ versions, Readable edges stored v →
        ∀ stored', (∀ x ∈ stored, x ∈ stored') →
          Readable edges stored' v)
    ∧ (∀ o w b1 b2 : Nat, pmeasured o w b1 = pmeasured o w b2)
    ∧ (incr rec add = full (rec ++ add)
        ∧ recheck rec = sfull rec)
    ∧ (bmin ws ≤ bmax ws ∧ bmin ws ∈ ws ∧ bmax ws ∈ ws)
    ∧ Adm (ra ++ ri ++ rb)
    ∧ (scheck (ra ++ ri ++ rb) = true
        → Safe (ra ++ ri ++ rb))
    ∧ (∀ g, recover (carry g) = qual g)
    ∧ ((reps ch datum.length).length
        = ch.length ^ datum.length) := by
  have h9 : bmin ws ≤ bmax ws ∧ bmin ws ∈ ws ∧ bmax ws ∈ ws := by
    have hex : ∃ v, v ∈ ws := by
      cases ws with
      | nil => exact absurd rfl hws
      | cons v ws' => exact ⟨v, List.mem_cons.mpr (Or.inl rfl)⟩
    obtain ⟨v, hv⟩ := hex
    obtain ⟨hlo, hhi⟩ := h_bsound ws v hv
    obtain ⟨hm1, hm2⟩ := h_battained ws hws
    exact ⟨Nat.le_trans hlo hhi, hm1, hm2⟩
  have h13 : (reps ch datum.length).length
      = ch.length ^ datum.length :=
    Persistence.finite ⟨ch, paxes⟩ datum.length
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h9, ?_, ?_, ?_, h13⟩
  · exact allsound axes req (ra ++ ri ++ rb) hcheck
  · intro cert t h
    exact ⟨certsound h, fun x => elim (certsound h)⟩
  · obtain ⟨r, hr⟩ := Persistence.existsmin hne
    have hr' : r ∈ reps ch datum.length
        ∧ ∀ s ∈ reps ch datum.length,
            ¬ Dominates paxes datum s r := hr
    exact ⟨r, hr'.1, hr⟩
  · intro r hr
    exact h_frontier paxes datum (reps ch datum.length) r hr
  · intro r h
    exact mincheck h
  · intro v _ hv stored' hsub
    exact readmono hv hsub
  · intro o w b1 b2
    exact profbaseline o w b1 b2
  · exact ⟨h_incr rec add, h_recheck rec⟩
  · exact h_adm hic (ra ++ ri) rb
      (h_adm hic ra ri hadm.1 hadm.2.1) hadm.2.2
  · intro h
    exact h_ssound _ h
  · exact h_carry

#print axioms additive
#print axioms projected
#print axioms split
#print axioms gapfree
#print axioms composed
#print axioms wholefree
#print axioms leterm
#print axioms subadd3
#print axioms compound
#print axioms localizes
#print axioms sound
#print axioms allsound
#print axioms gridlength
#print axioms spacefinite
#print axioms gapzero
#print axioms profbaseline
#print axioms leastcost
#print axioms tmem
#print axioms tretract
#print axioms onlycarrying
#print axioms joined

end Synthesis
