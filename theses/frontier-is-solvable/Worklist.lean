import Candidate
import Search
import Std

namespace Worklist

/- The closure worklist, stated against the landed frontier-home
   semantics. The least full closure is the search module's least
   saturation, here in its conjunctive-premise form: a term is in
   the closure when it is a seed term or it is the head of an
   admitted rule whose premises are all in the closure. Premise
   identity is term equality on natural numbers. A rule's premise
   list may carry duplicates; the saturation predicate reads the
   list up to membership, so duplicates are inert in the target
   semantics. The worklist therefore counts distinct premises:
   the distinct list of a premise list, defined below, has exactly
   the same membership and no duplicates.

   The candidate layer supplies the filter reading: a record is
   admitted exactly when it qualifies (seen and wanted), its
   premise links are its entry links, and its term is its entry
   term. The mapping from records to rules is defined at the end
   of this module; disqualified records contribute no rule, which
   matches the candidate module's dead-append result. -/

structure Rule where
  premises : List Nat
  head : Nat
deriving DecidableEq, Repr

/-- Distinct terms of a list: same membership, no duplicates. -/
def distinct : List Nat → List Nat
  | [] => []
  | p :: ps => if p ∈ distinct ps then distinct ps else p :: distinct ps

theorem mem_distinct {p : Nat} : ∀ {l : List Nat}, p ∈ distinct l ↔ p ∈ l := by
  intro l
  induction l with
  | nil => simp [distinct]
  | cons q qs ih =>
    by_cases hq : q ∈ distinct qs
    · have h1 : distinct (q :: qs) = distinct qs := by simp [distinct, hq]
      rw [h1]
      constructor
      · intro h; exact List.mem_cons_of_mem q (ih.mp h)
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · exact hq
        · exact ih.mpr h
    · have h1 : distinct (q :: qs) = q :: distinct qs := by simp [distinct, hq]
      rw [h1]
      simp only [List.mem_cons, ih]

theorem nodup_distinct : ∀ (l : List Nat), (distinct l).Nodup := by
  intro l
  induction l with
  | nil => simp [distinct]
  | cons q qs ih =>
    by_cases hq : q ∈ distinct qs
    · have h1 : distinct (q :: qs) = distinct qs := by simp [distinct, hq]
      rw [h1]; exact ih
    · have h1 : distinct (q :: qs) = q :: distinct qs := by simp [distinct, hq]
      rw [h1]
      exact List.nodup_cons.mpr ⟨hq, ih⟩

/-- The least full closure, seeded: the conjunctive-premise form
    of the search module's least saturation. -/
inductive DerivFrom (rules : List Rule) (seed : List Nat) : Nat → Prop where
  | base {x : Nat} (h : x ∈ seed) : DerivFrom rules seed x
  | fire {r : Rule} (hr : r ∈ rules) (h : ∀ p ∈ r.premises, DerivFrom rules seed p) :
      DerivFrom rules seed r.head

/-- The least full closure of a rule set, unseeded. -/
def Deriv (rules : List Rule) (x : Nat) : Prop := DerivFrom rules [] x

theorem derivFrom_mono_rules {rs rs' : List Rule} (h : ∀ r ∈ rs, r ∈ rs')
    {s : List Nat} {x : Nat} (hx : DerivFrom rs s x) : DerivFrom rs' s x := by
  induction hx with
  | base hb => exact DerivFrom.base hb
  | fire hr _ ih => exact DerivFrom.fire (h _ hr) ih

theorem derivFrom_mono_seed {rs : List Rule} {s s' : List Nat}
    (h : ∀ x ∈ s, x ∈ s') {x : Nat} (hx : DerivFrom rs s x) :
    DerivFrom rs s' x := by
  induction hx with
  | base hb => exact DerivFrom.base (h _ hb)
  | fire hr _ ih => exact DerivFrom.fire hr ih

/-- Leastness: the closure is contained in every seed-containing
    set closed under the rules. This is the saturation leastness
    of the search module, restated for conjunctive premises. -/
theorem derivFrom_least {rs : List Rule} {s : List Nat} {P : Nat → Prop}
    (hseed : ∀ x ∈ s, P x)
    (hclosed : ∀ r ∈ rs, (∀ p ∈ r.premises, P p) → P r.head)
    {x : Nat} (hx : DerivFrom rs s x) : P x := by
  induction hx with
  | base hb => exact hseed _ hb
  | fire hr _ ih => exact hclosed _ hr ih

/- The worklist state. The derived list is the current derived
   set, kept duplicate-free. The pending list is parallel to the
   rule list: its entry for a rule is that rule's distinct
   premises not yet processed. The queue holds derived terms not
   yet processed; the processed list holds those already visited.
   The remaining count of a rule is the length of its pending
   entry, so the count is a distinct-premise count by
   construction. -/
structure St where
  derived : List Nat
  pending : List (List Nat)
  queue : List Nat
  proc : List Nat

/-- The term-to-waiters index: the rules whose distinct premises
    contain the term. -/
def waiters (rules : List Rule) (t : Nat) : List Rule :=
  rules.filter (fun r => t ∈ distinct r.premises)

theorem mem_waiters {rules : List Rule} {t : Nat} {r : Rule} :
    r ∈ waiters rules t ↔ r ∈ rules ∧ t ∈ distinct r.premises := by
  simp [waiters, List.mem_filter]

/-- Heads of rules whose pending entry is empty and whose head is
    not yet derived, in rule order. -/
def fireHeads : List Rule → List (List Nat) → List Nat → List Nat
  | [], _, _ => []
  | _ :: _, [], _ => []
  | r :: rs, ps :: pss, D =>
    if ps = [] ∧ r.head ∉ D then r.head :: fireHeads rs pss D
    else fireHeads rs pss D

/-- Pairing of a rule with its pending entry. -/
def Paired : List Rule → List (List Nat) → Rule → List Nat → Prop
  | r :: rs, ps :: pss, r', ps' => (r = r' ∧ ps = ps') ∨ Paired rs pss r' ps'
  | _, _, _, _ => False

theorem paired_mem {rs : List Rule} {pend : List (List Nat)} {r : Rule}
    {ps : List Nat} (h : Paired rs pend r ps) : r ∈ rs := by
  induction rs generalizing pend with
  | nil => cases pend <;> simp [Paired] at h
  | cons r₀ rs ih =>
    cases pend with
    | nil => simp [Paired] at h
    | cons ps₀ pss =>
      simp only [Paired] at h
      rcases h with ⟨rfl, -⟩ | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem fireHeads_sound : ∀ {rs : List Rule} {pend : List (List Nat)}
    {D : List Nat} {x : Nat}, x ∈ fireHeads rs pend D →
    ∃ r ps, Paired rs pend r ps ∧ ps = [] ∧ r.head = x ∧ x ∉ D := by
  intro rs
  induction rs with
  | nil => intro pend D x h; cases pend <;> simp [fireHeads] at h
  | cons r rs ih =>
    intro pend D x h
    cases pend with
    | nil => simp [fireHeads] at h
    | cons ps pss =>
      simp only [fireHeads] at h
      by_cases hc : ps = [] ∧ r.head ∉ D
      · rw [if_pos hc] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨r, ps, Or.inl ⟨rfl, rfl⟩, hc.1, rfl, hc.2⟩
        · obtain ⟨r', ps', hp, hps, hh, hD⟩ := ih h
          exact ⟨r', ps', Or.inr hp, hps, hh, hD⟩
      · rw [if_neg hc] at h
        obtain ⟨r', ps', hp, hps, hh, hD⟩ := ih h
        exact ⟨r', ps', Or.inr hp, hps, hh, hD⟩

theorem fireHeads_complete : ∀ {rs : List Rule} {pend : List (List Nat)}
    {D : List Nat} {r : Rule} {ps : List Nat},
    Paired rs pend r ps → ps = [] → r.head ∉ D → r.head ∈ fireHeads rs pend D := by
  intro rs
  induction rs with
  | nil => intro pend D r ps h; cases pend <;> simp [Paired] at h
  | cons r₀ rs ih =>
    intro pend D r ps h hps hD
    cases pend with
    | nil => simp [Paired] at h
    | cons ps₀ pss =>
      simp only [Paired] at h
      simp only [fireHeads]
      rcases h with ⟨rfl, rfl⟩ | h
      · rw [if_pos ⟨hps, hD⟩]
        exact List.mem_cons_self
      · by_cases hc : ps₀ = [] ∧ r₀.head ∉ D
        · rw [if_pos hc]
          exact List.mem_cons_of_mem _ (ih h hps hD)
        · rw [if_neg hc]
          exact ih h hps hD

/-- The pending invariant: each pending entry is exactly the
    rule's distinct premises not yet processed. -/
def PendOk (proc : List Nat) : List Rule → List (List Nat) → Prop
  | [], [] => True
  | r :: rs, ps :: pss =>
    ps = (distinct r.premises).filter (fun p => p ∉ proc) ∧ PendOk proc rs pss
  | _, _ => False

/-- The firing invariant: a rule with an empty pending entry has
    its head derived. -/
def FireOk (D : List Nat) : List Rule → List (List Nat) → Prop
  | [], [] => True
  | r :: rs, ps :: pss => (ps = [] → r.head ∈ D) ∧ FireOk D rs pss
  | _, _ => False

theorem pendOk_paired {proc : List Nat} : ∀ {rs : List Rule}
    {pend : List (List Nat)} {r : Rule} {ps : List Nat},
    PendOk proc rs pend → Paired rs pend r ps →
    ps = (distinct r.premises).filter (fun p => p ∉ proc) := by
  intro rs
  induction rs with
  | nil => intro pend r ps h hp; cases pend <;> simp [PendOk, Paired] at hp
  | cons r₀ rs ih =>
    intro pend r ps h hp
    cases pend with
    | nil => simp [PendOk] at h
    | cons ps₀ pss =>
      simp only [PendOk] at h
      simp only [Paired] at hp
      rcases hp with ⟨rfl, rfl⟩ | hp
      · exact h.1
      · exact ih h.2 hp

theorem fireOk_paired {D : List Nat} : ∀ {rs : List Rule}
    {pend : List (List Nat)} {r : Rule} {ps : List Nat},
    FireOk D rs pend → Paired rs pend r ps → ps = [] → r.head ∈ D := by
  intro rs
  induction rs with
  | nil => intro pend r ps h hp; cases pend <;> simp [FireOk, Paired] at hp
  | cons r₀ rs ih =>
    intro pend r ps h hp hps
    cases pend with
    | nil => simp [FireOk] at h
    | cons ps₀ pss =>
      simp only [FireOk] at h
      simp only [Paired] at hp
      rcases hp with ⟨rfl, rfl⟩ | hp
      · exact h.1 hps
      · exact ih h.2 hp hps

theorem filter_not_mem {a : Nat} {l : List Nat} (h : a ∉ l) :
    l.filter (fun p => p ≠ a) = l := by
  rw [List.filter_eq_self]
  intro x hx
  simp only [decide_eq_true_eq]
  exact fun hxa => h (hxa ▸ hx)

/-- Filtering a newly processed term out of a filtered distinct
    list is filtering against the grown processed list. -/
theorem filter_filter_proc {t : Nat} {proc : List Nat} (l : List Nat) :
    (l.filter (fun p => p ∉ proc)).filter (fun p => p ≠ t) =
      l.filter (fun p => p ∉ t :: proc) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases hx1 : x ∈ proc <;> by_cases hx2 : x = t <;> simp_all

theorem pendOk_step {rules : List Rule} {pend : List (List Nat)}
    {proc : List Nat} {t : Nat}
    (h : PendOk proc rules pend) :
    PendOk (t :: proc) rules (pend.map (fun ps => ps.filter (fun p => p ≠ t))) := by
  induction rules generalizing pend with
  | nil =>
    cases pend with
    | nil => exact True.intro
    | cons ps pss => simp [PendOk] at h
  | cons r rs ih =>
    cases pend with
    | nil => simp [PendOk] at h
    | cons ps pss =>
      refine ⟨?_, ih h.2⟩
      show ps.filter (fun p => p ≠ t) =
        (distinct r.premises).filter (fun p => p ∉ t :: proc)
      rw [h.1]
      exact filter_filter_proc _

theorem pendOk_seed {rules : List Rule} {S : List Nat} :
    PendOk S rules
      (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S))) := by
  induction rules with
  | nil => exact True.intro
  | cons r rs ih =>
    simp only [List.map_cons, PendOk]
    exact ⟨True.intro, ih⟩

theorem fireOk_mono {D D' : List Nat} (h : ∀ x ∈ D, x ∈ D') :
    ∀ {rs : List Rule} {pend : List (List Nat)},
    FireOk D rs pend → FireOk D' rs pend := by
  intro rs
  induction rs with
  | nil => intro pend hf; cases pend <;> exact hf
  | cons r rs ih =>
    intro pend hf
    cases pend with
    | nil => exact hf
    | cons ps pss =>
      simp only [FireOk] at hf ⊢
      exact ⟨fun hh => h _ (hf.1 hh), ih hf.2⟩

theorem paired_map_filter {rules : List Rule} {pend : List (List Nat)}
    {t : Nat} : ∀ {r : Rule} {ps' : List Nat},
    Paired rules (pend.map (fun q => q.filter (fun p => p ≠ t))) r ps' →
    ∃ ps, Paired rules pend r ps ∧ ps' = ps.filter (fun p => p ≠ t) := by
  induction rules generalizing pend with
  | nil => intro r ps' h; cases pend <;> simp [Paired] at h
  | cons r₀ rs ih =>
    intro r ps' h
    cases pend with
    | nil => simp [Paired] at h
    | cons ps₀ pss =>
      simp only [List.map_cons, Paired] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨ps₀, Or.inl ⟨rfl, rfl⟩, rfl⟩
      · obtain ⟨ps₁, hp, rfl⟩ := ih h
        exact ⟨ps₁, Or.inr hp, rfl⟩

theorem paired_of_mem {rules : List Rule} {pend : List (List Nat)}
    (hlen : pend.length = rules.length) :
    ∀ {r : Rule}, r ∈ rules →
    ∃ ps, Paired rules pend r ps := by
  induction rules generalizing pend with
  | nil => intro r hr; simp at hr
  | cons r₀ rs ih =>
    intro r hr
    cases pend with
    | nil => simp at hlen
    | cons ps₀ pss =>
      have hlen' : pss.length = rs.length := by
        simpa using hlen
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨ps₀, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨ps, hp⟩ := ih hlen' hr
        exact ⟨ps, Or.inr hp⟩

theorem pend_length {proc : List Nat} : ∀ {rs : List Rule}
    {pend : List (List Nat)}, PendOk proc rs pend → pend.length = rs.length := by
  intro rs
  induction rs with
  | nil =>
    intro pend h
    cases pend with
    | nil => rfl
    | cons ps pss => exact False.elim h
  | cons r rs ih =>
    intro pend h
    cases pend with
    | nil => simp [PendOk] at h
    | cons ps pss =>
      simp only [PendOk] at h
      simp [ih h.2]

/-- One queue step: process the head term, erase it from every
    pending entry (by the waiters theorem below, entries of
    non-waiter rules are unchanged, so this visits exactly the
    waiters semantically), fire every rule whose count reaches
    zero, and enqueue the newly derived heads once each. -/
def step (rules : List Rule) (s : St) : St :=
  match s.queue with
  | [] => s
  | t :: q =>
    let pend' := s.pending.map (fun ps => ps.filter (fun p => p ≠ t))
    let nh := distinct (fireHeads rules pend' s.derived)
    { derived := s.derived ++ nh
      pending := pend'
      queue := q ++ nh
      proc := t :: s.proc }

def go : Nat → List Rule → St → St
  | 0, _, s => s
  | fuel + 1, rules, s =>
    if s.queue = [] then s else go fuel rules (step rules s)

/-- Seeding for a fixed view: pending counts are computed against
    the seed set, zero-premise and already-satisfied rules fire at
    once, and their heads form the initial queue. -/
def seedSt (rules : List Rule) (S : List Nat) : St :=
  let pend := rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S))
  let nh := distinct (fireHeads rules pend S)
  { derived := S ++ nh
    pending := pend
    queue := nh
    proc := S }

/-- Admitting rules at an append is seeding the grown rule list
    against the carried derived set: old rules keep the counts
    their carried pending entries already encode, since pending
    entries are a function of the processed set alone. -/
def admitSt (rules : List Rule) (D : List Nat) : St := seedSt rules D

theorem pendOk_admit {rules : List Rule} {pend : List (List Nat)}
    {D : List Nat} (h : PendOk D rules pend) :
    pend = (admitSt rules D).pending := by
  have h2 : ∀ {rs : List Rule} {pd : List (List Nat)},
      PendOk D rs pd →
      pd = rs.map (fun r => (distinct r.premises).filter (fun p => p ∉ D)) := by
    intro rs
    induction rs with
    | nil =>
      intro pd hp
      cases pd with
      | nil => rfl
      | cons ps pss => exact False.elim hp
    | cons r rs ih =>
      intro pd hp
      cases pd with
      | nil => simp [PendOk] at hp
      | cons ps pss =>
        simp only [PendOk, List.map_cons] at hp ⊢
        rw [hp.1, ih hp.2]
  exact h2 h

/-- Waiters only: processing a term changes the pending entry of
    a rule only when the rule waits on that term. -/
theorem waiters_only {rules : List Rule} {pend : List (List Nat)}
    {proc : List Nat} {t : Nat} (hok : PendOk proc rules pend)
    {r : Rule} {ps : List Nat} (hp : Paired rules pend r ps)
    (hw : r ∉ waiters rules t) : ps.filter (fun p => p ≠ t) = ps := by
  have hps := pendOk_paired hok hp
  have ht : t ∉ distinct r.premises := by
    intro hm
    exact hw (mem_waiters.mpr ⟨paired_mem hp, hm⟩)
  have ht2 : t ∉ ps := by
    rw [hps]
    intro hm
    exact ht ((List.mem_filter.mp hm).1)
  exact filter_not_mem ht2


theorem nodup_append_of_disjoint {a b : List Nat} (ha : a.Nodup) (hb : b.Nodup)
    (hd : ∀ x ∈ a, x ∉ b) : (a ++ b).Nodup := by
  induction a with
  | nil => simpa using hb
  | cons x xs ih =>
    rw [List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,
      ih (List.nodup_cons.mp ha).2 (fun y hy => hd y (List.mem_cons_of_mem x hy))⟩
    intro hm
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · exact (List.nodup_cons.mp ha).1 hm
    · exact hd x List.mem_cons_self hm

theorem length_erase_of_mem' {a : Nat} : ∀ {l : List Nat}, a ∈ l →
    (l.erase a).length + 1 = l.length := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons b bs ih =>
    intro h
    by_cases hb : b = a
    · subst hb
      simp [List.erase]
    · have hmem : a ∈ bs := by
        rcases List.mem_cons.mp h with rfl | h'
        · exact absurd rfl hb
        · exact h'
      have hba : (b == a) = false := by simp [hb]
      have he : (b :: bs).erase a = b :: bs.erase a := by simp [List.erase, hba]
      have hih := ih hmem
      rw [he]
      simp only [List.length_cons]
      omega

theorem mem_erase_of_ne' {a b : Nat} (h : a ≠ b) : ∀ {l : List Nat},
    a ∈ l → a ∈ l.erase b := by
  intro l
  induction l with
  | nil => intro hh; simp at hh
  | cons c cs ih =>
    intro hh
    by_cases hc : c = b
    · subst hc
      rcases List.mem_cons.mp hh with rfl | hh'
      · exact absurd rfl h
      · simpa [List.erase] using hh'
    · have hcb : (c == b) = false := by simp [hc]
      have he : (c :: cs).erase b = c :: cs.erase b := by simp [List.erase, hcb]
      rw [he]
      rcases List.mem_cons.mp hh with rfl | hh'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hh')

theorem nodup_erase' {a : Nat} : ∀ {l : List Nat}, l.Nodup → (l.erase a).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons b bs ih =>
    intro h
    by_cases hb : b = a
    · subst hb
      simpa [List.erase] using (List.nodup_cons.mp h).2
    · have hba : (b == a) = false := by simp [hb]
      have he : (b :: bs).erase a = b :: bs.erase a := by simp [List.erase, hba]
      rw [he]
      refine List.nodup_cons.mpr ⟨?_, ih (List.nodup_cons.mp h).2⟩
      intro hm
      exact (List.nodup_cons.mp h).1 (List.mem_of_mem_erase hm)

theorem length_le_of_subset {a b : List Nat} (ha : a.Nodup) (hb : b.Nodup)
    (h : ∀ x ∈ a, x ∈ b) : a.length ≤ b.length := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∈ b := h x List.mem_cons_self
    have hxs : ∀ y ∈ xs, y ∈ b.erase x := by
      intro y hy
      have hyx : y ≠ x := fun hh => (List.nodup_cons.mp ha).1 (hh ▸ hy)
      exact mem_erase_of_ne' hyx (h y (List.mem_cons_of_mem x hy))
    have h1 := ih (List.nodup_cons.mp ha).2 (nodup_erase' hb) hxs
    have h2 := length_erase_of_mem' hx
    simp only [List.length_cons]
    omega

theorem filter_nil_of_all {l : List Nat} {P : List Nat}
    (h : ∀ p ∈ l, p ∈ P) : l.filter (fun p => p ∉ P) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp [h x hx]

theorem all_eq_of_filter_nil {l : List Nat} {t : Nat}
    (h : l.filter (fun p => p ≠ t) = []) : ∀ p ∈ l, p = t := by
  intro p hp
  cases Decidable.em (p = t) with
  | inl hpt => exact hpt
  | inr hc =>
    exfalso
    have hm : p ∈ l.filter (fun p => p ≠ t) := by
      apply List.mem_filter.mpr
      exact ⟨hp, by simp only [decide_eq_true_eq]; exact hc⟩
    rw [h] at hm
    exact List.not_mem_nil hm

theorem fireOk_of_forall {D : List Nat} : ∀ {rs : List Rule}
    {pend : List (List Nat)}, pend.length = rs.length →
    (∀ r ps, Paired rs pend r ps → ps = [] → r.head ∈ D) →
    FireOk D rs pend := by
  intro rs
  induction rs with
  | nil =>
    intro pend hlen _
    cases pend with
    | nil => exact True.intro
    | cons ps pss => simp at hlen
  | cons r rs ih =>
    intro pend hlen h
    cases pend with
    | nil => simp at hlen
    | cons ps pss =>
      have hlen' : pss.length = rs.length := by simpa using hlen
      simp only [FireOk]
      refine ⟨fun hh => h r ps (Or.inl ⟨rfl, rfl⟩) hh, ih hlen' ?_⟩
      intro r' ps' hp hps
      exact h r' ps' (Or.inr hp) hps

/-- The invariant bundle carried by every worklist state. -/
def Inv (rules : List Rule) (S bound : List Nat) (s : St) : Prop :=
  PendOk s.proc rules s.pending ∧
  FireOk s.derived rules s.pending ∧
  (∀ x ∈ s.derived, DerivFrom rules S x) ∧
  s.derived.Nodup ∧ s.queue.Nodup ∧ s.proc.Nodup ∧
  (∀ x ∈ s.derived, x ∈ s.queue ∨ x ∈ s.proc) ∧
  (∀ x ∈ s.queue, x ∉ s.proc) ∧
  (∀ x ∈ s.derived, x ∈ bound) ∧
  (∀ x ∈ s.queue, x ∈ s.derived) ∧
  (∀ x ∈ s.proc, x ∈ s.derived) ∧
  (∀ x ∈ S, x ∈ s.proc) ∧
  s.pending.length = rules.length

theorem seedSt_derived {rules : List Rule} {S : List Nat} :
    (seedSt rules S).derived =
      S ++ distinct (fireHeads rules
        (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S))) S) := rfl

theorem seedSt_pending {rules : List Rule} {S : List Nat} :
    (seedSt rules S).pending =
      rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S)) := rfl

theorem inv_seed {rules : List Rule} {S bound : List Nat}
    (_hb : bound.Nodup) (hS : S.Nodup)
    (hSb : ∀ x ∈ S, x ∈ bound) (hrb : ∀ r ∈ rules, r.head ∈ bound) :
    Inv rules S bound (seedSt rules S) := by
  have hpend : PendOk S rules
      (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S))) :=
    pendOk_seed
  have hlen : (rules.map (fun r => (distinct r.premises).filter
      (fun p => p ∉ S))).length = rules.length := by simp
  have hfire : FireOk (S ++ distinct (fireHeads rules
      (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S))) S))
      rules (rules.map (fun r => (distinct r.premises).filter
        (fun p => p ∉ S))) := by
    apply fireOk_of_forall hlen
    intro r ps hp hps
    by_cases hm : r.head ∈ S
    · exact List.mem_append.mpr (Or.inl hm)
    · have hhead : r.head ∈ fireHeads rules
          (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S))) S :=
        fireHeads_complete hp hps hm
      exact List.mem_append.mpr (Or.inr (mem_distinct.mpr hhead))
  refine ⟨hpend, hfire, ?_, ?_, nodup_distinct _, hS, ?_, ?_, ?_, ?_, ?_, ?_, hlen⟩
  · intro x hx
    rw [seedSt_derived] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact DerivFrom.base hx
    · have hx' : x ∈ fireHeads rules
          (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S))) S :=
        mem_distinct.mp hx
      obtain ⟨r, ps, hp, hps, rfl, hxS⟩ := fireHeads_sound hx'
      have hps' := pendOk_paired hpend hp
      have hprem : ∀ p ∈ r.premises, p ∈ S := by
        intro p hpp
        cases Decidable.em (p ∈ S) with
        | inl hps2 => exact hps2
        | inr hpc =>
          exfalso
          have hmem : p ∈ (distinct r.premises).filter (fun q => q ∉ S) := by
            apply List.mem_filter.mpr
            exact ⟨mem_distinct.mpr hpp, by
              simp only [decide_eq_true_eq]; exact hpc⟩
          rw [← hps', hps] at hmem
          exact List.not_mem_nil hmem
      exact DerivFrom.fire (paired_mem hp) (fun p hpp => DerivFrom.base (hprem p hpp))
  · apply nodup_append_of_disjoint hS (nodup_distinct _)
    intro x hxS hxnh
    have hx' : x ∈ fireHeads rules
        (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S))) S :=
      mem_distinct.mp hxnh
    obtain ⟨r, ps, hp, hps, rfl, hxS'⟩ := fireHeads_sound hx'
    exact hxS' hxS
  · intro x hx
    rw [seedSt_derived] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl hx
  · intro x hx hxS
    have hx' : x ∈ fireHeads rules
        (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S))) S :=
      mem_distinct.mp hx
    obtain ⟨r, ps, hp, hps, rfl, hxS'⟩ := fireHeads_sound hx'
    exact hxS' hxS
  · intro x hx
    rw [seedSt_derived] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hSb x hx
    · have hx' : x ∈ fireHeads rules
          (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S))) S :=
        mem_distinct.mp hx
      obtain ⟨r, ps, hp, hps, rfl, hxS'⟩ := fireHeads_sound hx'
      exact hrb r (paired_mem hp)
  · intro x hx
    exact List.mem_append.mpr (Or.inr hx)
  · intro x hx
    exact List.mem_append.mpr (Or.inl hx)
  · intro x hx
    exact hx

theorem step_eq {rules : List Rule} {s : St} {t : Nat} {q : List Nat}
    (hq : s.queue = t :: q) :
    step rules s =
      { derived := s.derived ++ distinct (fireHeads rules
          (s.pending.map (fun ps => ps.filter (fun p => p ≠ t))) s.derived)
        pending := s.pending.map (fun ps => ps.filter (fun p => p ≠ t))
        queue := q ++ distinct (fireHeads rules
          (s.pending.map (fun ps => ps.filter (fun p => p ≠ t))) s.derived)
        proc := t :: s.proc } := by
  unfold step
  rw [hq]

theorem inv_step {rules : List Rule} {S bound : List Nat} {s : St}
    (hinv : Inv rules S bound s) (hrb : ∀ r ∈ rules, r.head ∈ bound)
    {t : Nat} {q : List Nat} (hq : s.queue = t :: q) :
    Inv rules S bound (step rules s) := by
  obtain ⟨hpend, hfire, hsound, hdnd, hqnd, hpnd, hcover, hdisj, hbound,
    hqsub, hpsub, hseed, hlen⟩ := hinv
  have htq : t ∈ s.queue := by
    rw [hq]
    exact List.mem_cons_self
  have htD : t ∈ s.derived := hqsub t htq
  have htP : t ∉ s.proc := hdisj t htq
  have hqnd' : t ∉ q ∧ q.Nodup := by
    have h := hqnd
    rw [hq] at h
    exact List.nodup_cons.mp h
  have hpend' : PendOk (t :: s.proc) rules
      (s.pending.map (fun ps => ps.filter (fun p => p ≠ t))) := pendOk_step hpend
  have hlen' : (s.pending.map (fun ps => ps.filter (fun p => p ≠ t))).length
      = rules.length := by rw [List.length_map]; exact hlen
  rw [step_eq hq]
  refine ⟨hpend', ?_, ?_, ?_, ?_, List.nodup_cons.mpr ⟨htP, hpnd⟩, ?_, ?_, ?_, ?_, ?_,
    fun x hx => List.mem_cons_of_mem t (hseed x hx), hlen'⟩
  · -- firing invariant after the step
    apply fireOk_of_forall hlen'
    intro r ps' hp' hps'
    obtain ⟨ps, hp, rfl⟩ := paired_map_filter hp'
    by_cases hps : ps = []
    · have hh := fireOk_paired hfire hp hps
      exact List.mem_append.mpr (Or.inl hh)
    · have hprem : ∀ p ∈ r.premises, p ∈ t :: s.proc := by
        intro p hpp
        have hpd : p ∈ distinct r.premises := mem_distinct.mpr hpp
        by_cases hpp' : p ∈ s.proc
        · exact List.mem_cons_of_mem t hpp'
        · have hps_eq := pendOk_paired hpend hp
          have hpm : p ∈ ps := by
            rw [hps_eq]
            apply List.mem_filter.mpr
            exact ⟨hpd, by simp only [decide_eq_true_eq]; exact hpp'⟩
          have hpt : p = t := all_eq_of_filter_nil hps' p hpm
          show p ∈ t :: s.proc
          rw [hpt]
          exact List.mem_cons_self
      by_cases hh : r.head ∈ s.derived
      · exact List.mem_append.mpr (Or.inl hh)
      · have hfh : r.head ∈ fireHeads rules
            (s.pending.map (fun ps => ps.filter (fun p => p ≠ t))) s.derived :=
          fireHeads_complete hp' hps' hh
        exact List.mem_append.mpr (Or.inr (mem_distinct.mpr hfh))
  · -- soundness after the step
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hsound x hx
    · obtain ⟨r, ps', hp', hps', rfl, hxD⟩ := fireHeads_sound (mem_distinct.mp hx)
      have hps_eq := pendOk_paired hpend' hp'
      refine DerivFrom.fire (paired_mem hp') ?_
      intro p hpp
      have hpd : p ∈ distinct r.premises := mem_distinct.mpr hpp
      have hpD : p ∈ s.derived := by
        by_cases hpm : p ∈ t :: s.proc
        · rcases List.mem_cons.mp hpm with rfl | hpm
          · exact htD
          · exact hpsub p hpm
        · have hmem : p ∈ (distinct r.premises).filter (fun q => q ∉ t :: s.proc) :=
            List.mem_filter.mpr ⟨hpd, by simp [hpm]⟩
          rw [← hps_eq, hps'] at hmem
          simp at hmem
      exact hsound p hpD
  · -- derived stays duplicate-free
    apply nodup_append_of_disjoint hdnd (nodup_distinct _)
    intro x hxD hxnh
    obtain ⟨r, ps', hp', hps', rfl, hxD'⟩ := fireHeads_sound (mem_distinct.mp hxnh)
    exact hxD' hxD
  · -- queue stays duplicate-free
    apply nodup_append_of_disjoint hqnd'.2 (nodup_distinct _)
    intro x hxq hxnh
    obtain ⟨r, ps', hp', hps', rfl, hxD'⟩ := fireHeads_sound (mem_distinct.mp hxnh)
    have hxm : r.head ∈ s.queue := by
      rw [hq]
      exact List.mem_cons_of_mem t hxq
    exact hxD' (hqsub _ hxm)
  · -- coverage after the step
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · rcases hcover x hx with hxc | hxc
      · rw [hq] at hxc
        rcases List.mem_cons.mp hxc with rfl | hxc
        · exact Or.inr List.mem_cons_self
        · exact Or.inl (List.mem_append.mpr (Or.inl hxc))
      · exact Or.inr (List.mem_cons_of_mem t hxc)
    · exact Or.inl (List.mem_append.mpr (Or.inr hx))
  · -- queue and processed stay disjoint
    intro x hx hxproc
    rw [List.mem_append] at hx
    rcases List.mem_cons.mp hxproc with rfl | hxproc
    · rcases hx with hx | hx
      · exact hqnd'.1 hx
      · obtain ⟨r, ps', hp', hps', rfl, hxD'⟩ := fireHeads_sound (mem_distinct.mp hx)
        exact hxD' htD
    · rcases hx with hx | hx
      · have hxm : x ∈ s.queue := by
          rw [hq]
          exact List.mem_cons_of_mem t hx
        exact hdisj x hxm hxproc
      · obtain ⟨r, ps', hp', hps', rfl, hxD'⟩ := fireHeads_sound (mem_distinct.mp hx)
        exact hxD' (hpsub _ hxproc)
  · -- derived stays inside the bound
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hbound x hx
    · obtain ⟨r, ps', hp', hps', rfl, hxD'⟩ := fireHeads_sound (mem_distinct.mp hx)
      exact hrb r (paired_mem hp')
  · -- queue stays inside derived
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have hxm : x ∈ s.queue := by
        rw [hq]
        exact List.mem_cons_of_mem t hx
      exact List.mem_append.mpr (Or.inl (hqsub x hxm))
    · exact List.mem_append.mpr (Or.inr hx)
  · -- processed stays inside derived
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_append.mpr (Or.inl htD)
    · exact List.mem_append.mpr (Or.inl (hpsub x hx))

theorem go_succ (fuel : Nat) (rules : List Rule) (s : St) :
    go (fuel + 1) rules s =
      if s.queue = [] then s else go fuel rules (step rules s) := by
  simp only [go]

theorem go_spec : ∀ (fuel : Nat) {rules : List Rule} {S bound : List Nat}
    (s : St), Inv rules S bound s → bound.Nodup →
    (∀ r ∈ rules, r.head ∈ bound) →
    bound.length - s.derived.length + s.queue.length ≤ fuel →
    Inv rules S bound (go fuel rules s) ∧ (go fuel rules s).queue = [] ∧
    (∀ x ∈ s.derived, x ∈ (go fuel rules s).derived) ∧
    (∀ x ∈ s.proc, x ∈ (go fuel rules s).proc) := by
  intro fuel
  induction fuel with
  | zero =>
    intro rules S bound s hinv _ _ hm
    have hq : s.queue = [] := by
      cases hqe : s.queue with
      | nil => rfl
      | cons t q =>
        have h1 : 1 ≤ s.queue.length := by rw [hqe]; simp
        omega
    exact ⟨hinv, hq, fun x hx => hx, fun x hx => hx⟩
  | succ fuel ih =>
    intro rules S bound s hinv hb hrb hm
    cases hqe : s.queue with
    | nil =>
      rw [go_succ, if_pos hqe]
      exact ⟨hinv, hqe, fun x hx => hx, fun x hx => hx⟩
    | cons t q =>
      have hne : ¬ s.queue = [] := by simp [hqe]
      rw [go_succ, if_neg hne]
      have hinv' := inv_step hinv hrb hqe
      have hdlen : (step rules s).derived.length =
          s.derived.length + (distinct (fireHeads rules
            (s.pending.map (fun ps => ps.filter (fun p => p ≠ t)))
            s.derived)).length := by
        rw [step_eq hqe]
        simp [List.length_append]
      have hqlen : (step rules s).queue.length =
          q.length + (distinct (fireHeads rules
            (s.pending.map (fun ps => ps.filter (fun p => p ≠ t)))
            s.derived)).length := by
        rw [step_eq hqe]
        simp [List.length_append]
      have hle : (step rules s).derived.length ≤ bound.length :=
        length_le_of_subset hinv'.2.2.2.1 hb hinv'.2.2.2.2.2.2.2.2.1
      have hm' : bound.length - (step rules s).derived.length +
          (step rules s).queue.length ≤ fuel := by
        have hsq : s.queue.length = q.length + 1 := by rw [hqe]; simp
        omega
      obtain ⟨h1, h2, h3, h4⟩ := ih (step rules s) hinv' hb hrb hm'
      refine ⟨h1, h2, ?_, ?_⟩
      · intro x hx
        apply h3
        rw [step_eq hqe]
        exact List.mem_append.mpr (Or.inl hx)
      · intro x hx
        apply h4
        rw [step_eq hqe]
        exact List.mem_cons_of_mem t hx

theorem complete_of_inv {rules : List Rule} {S bound : List Nat} {s : St}
    (hinv : Inv rules S bound s) (hq : s.queue = []) {x : Nat}
    (hx : DerivFrom rules S x) : x ∈ s.derived := by
  obtain ⟨hpend, hfire, hsound, hdnd, hqnd, hpnd, hcover, hdisj, hbound,
    hqsub, hpsub, hseed, hlen⟩ := hinv
  induction hx with
  | base hb => exact hpsub _ (hseed _ hb)
  | fire hr h ih =>
    obtain ⟨ps, hp⟩ := paired_of_mem hlen hr
    have hps_eq := pendOk_paired hpend hp
    have hps : ps = [] := by
      rw [hps_eq]
      apply filter_nil_of_all
      intro p hpd
      have hpD : p ∈ s.derived := ih p (mem_distinct.mp hpd)
      rcases hcover p hpD with hpc | hpc
      · rw [hq] at hpc
        simp at hpc
      · exact hpc
    exact fireOk_paired hfire hp hps

/-- Fixed view, seeded form: the drained worklist's derived set
    is exactly the least full closure. -/
theorem worklist_eq {rules : List Rule} {S bound : List Nat}
    (hb : bound.Nodup) (hS : S.Nodup)
    (hSb : ∀ x ∈ S, x ∈ bound) (hrb : ∀ r ∈ rules, r.head ∈ bound)
    {fuel : Nat} (hfuel : bound.length - S.length ≤ fuel) {x : Nat} :
    x ∈ (go fuel rules (seedSt rules S)).derived ↔ DerivFrom rules S x := by
  have hinv0 := inv_seed hb hS hSb hrb
  have hdlen : (seedSt rules S).derived.length =
      S.length + (distinct (fireHeads rules
        (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S)))
        S)).length := by
    rw [seedSt_derived, List.length_append]
  have hqlen : (seedSt rules S).queue.length =
      (distinct (fireHeads rules
        (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S)))
        S)).length := rfl
  have hle : (seedSt rules S).derived.length ≤ bound.length :=
    length_le_of_subset hinv0.2.2.2.1 hb hinv0.2.2.2.2.2.2.2.2.1
  have hm : bound.length - (seedSt rules S).derived.length +
      (seedSt rules S).queue.length ≤ fuel := by omega
  obtain ⟨hinv, hq, -, -⟩ := go_spec fuel (seedSt rules S) hinv0 hb hrb hm
  constructor
  · intro hx
    exact hinv.2.2.1 x hx
  · intro hx
    exact complete_of_inv hinv hq hx

/-- Fixed view, unseeded: the worklist closure is the least full
    closure of the rule set. -/
theorem worklist_closure {rules : List Rule} {bound : List Nat}
    (hb : bound.Nodup) (hrb : ∀ r ∈ rules, r.head ∈ bound)
    {fuel : Nat} (hfuel : bound.length ≤ fuel) {x : Nat} :
    x ∈ (go fuel rules (seedSt rules [])).derived ↔ Deriv rules x :=
  worklist_eq hb (by simp) (by simp) hrb (by simpa using hfuel)

/-- Termination at a finite term bound: with fuel at least the
    bound's size the queue drains, the derived set is
    duplicate-free, and every derived term has been processed
    exactly once (it sits in the duplicate-free processed list
    and in no queue). -/
theorem terminates {rules : List Rule} {S bound : List Nat}
    (hb : bound.Nodup) (hS : S.Nodup)
    (hSb : ∀ x ∈ S, x ∈ bound) (hrb : ∀ r ∈ rules, r.head ∈ bound) :
    (go bound.length rules (seedSt rules S)).queue = [] ∧
    (go bound.length rules (seedSt rules S)).derived.Nodup ∧
    (∀ x ∈ (go bound.length rules (seedSt rules S)).derived,
      x ∈ (go bound.length rules (seedSt rules S)).proc) ∧
    (go bound.length rules (seedSt rules S)).proc.Nodup := by
  have hinv0 := inv_seed hb hS hSb hrb
  have hdlen : (seedSt rules S).derived.length =
      S.length + (distinct (fireHeads rules
        (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S)))
        S)).length := by
    rw [seedSt_derived, List.length_append]
  have hle : (seedSt rules S).derived.length ≤ bound.length :=
    length_le_of_subset hinv0.2.2.2.1 hb hinv0.2.2.2.2.2.2.2.2.1
  have hm : bound.length - (seedSt rules S).derived.length +
      (seedSt rules S).queue.length ≤ bound.length := by
    have hq : (seedSt rules S).queue.length =
        (distinct (fireHeads rules
          (rules.map (fun r => (distinct r.premises).filter (fun p => p ∉ S)))
          S)).length := rfl
    omega
  obtain ⟨hinv, hq, -, -⟩ := go_spec bound.length (seedSt rules S) hinv0 hb hrb hm
  refine ⟨hq, hinv.2.2.2.1, ?_, hinv.2.2.2.2.2.1⟩
  intro x hx
  rcases hinv.2.2.2.2.2.2.1 x hx with hxc | hxc
  · rw [hq] at hxc
    simp at hxc
  · exact hxc

/-- The canonical derivation predicate, restated in this home
    exactly as the canonical layer states it: roots and
    finite-premise edges, least closure. -/
inductive GDerives (B : Nat → Prop) (R : List Nat → Nat → Prop) : Nat → Prop where
  | root {a : Nat} : B a → GDerives B R a
  | step {ps : List Nat} {a : Nat} : R ps a →
      (∀ p, p ∈ ps → GDerives B R p) → GDerives B R a

def edgeOf (rules : List Rule) (ps : List Nat) (a : Nat) : Prop :=
  ∃ r, r ∈ rules ∧ r.premises = ps ∧ r.head = a

/-- The worklist closure is the canonical closure of the graph
    whose edges are exactly the rule set and whose roots are
    empty: the canonical layer's view has no roots, and its
    zero-premise records are edges with an empty premise list. -/
theorem deriv_iff_gderives {rules : List Rule} {x : Nat} :
    Deriv rules x ↔ GDerives (fun _ => False) (edgeOf rules) x := by
  constructor
  · intro hx
    induction hx with
    | base hb => simp at hb
    | fire hr _ ih =>
      exact GDerives.step ⟨_, hr, rfl, rfl⟩ ih
  · intro hx
    induction hx with
    | root hb => exact hb.elim
    | step he _ ih =>
      obtain ⟨r, hr, rfl, rfl⟩ := he
      exact DerivFrom.fire hr ih

def ruleOfEdge (e : List Nat × Nat) : Rule := ⟨e.1, e.2⟩

theorem edgeOf_map {es : List (List Nat × Nat)} {ps : List Nat} {a : Nat} :
    edgeOf (es.map ruleOfEdge) ps a ↔ (ps, a) ∈ es := by
  constructor
  · rintro ⟨r, hr, hps, ha⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    cases e with
    | mk ps' a' =>
      simp only [ruleOfEdge] at hps ha
      rw [← hps, ← ha]
      exact he
  · intro h
    exact ⟨ruleOfEdge (ps, a), List.mem_map.mpr ⟨(ps, a), h, rfl⟩, rfl, rfl⟩

/-- One direction of the append form, standalone: a derivation
    from the carried derived set over the grown rule list is a
    derivation over the grown list from no seed, because every
    carried term is derivable from the old list and the old list
    sits inside the grown list. -/
theorem derivFrom_append_of_seed {rs₁ rs₂ : List Rule} {D₁ : List Nat}
    (hD : ∀ y, y ∈ D₁ ↔ Deriv rs₁ y) {x : Nat}
    (hx : DerivFrom (rs₁ ++ rs₂) D₁ x) : Deriv (rs₁ ++ rs₂) x := by
  induction hx with
  | base hb =>
    exact derivFrom_mono_rules (fun r hr => List.mem_append_left rs₂ hr)
      ((hD _).mp hb)
  | fire hr _ ih => exact DerivFrom.fire hr ih

/-- Append form: seeding the grown rule list against the carried
    derived set of the old list gives exactly the least full
    closure of the grown list. Rules incomplete before the append
    are the old rules whose pending entries are nonempty against
    the carried set; the seeding recomputes exactly those entries
    from the carried set, so nothing about them is lost or
    restarted. -/
theorem append_eq {rs₁ rs₂ : List Rule} {bound : List Nat}
    (hb : bound.Nodup) {D₁ : List Nat} (hD₁nd : D₁.Nodup)
    (hDb : ∀ x ∈ D₁, x ∈ bound)
    (hrb : ∀ r ∈ rs₁ ++ rs₂, r.head ∈ bound)
    (hD : ∀ y, y ∈ D₁ ↔ Deriv rs₁ y)
    {fuel : Nat} (hfuel : bound.length - D₁.length ≤ fuel) {x : Nat} :
    x ∈ (go fuel (rs₁ ++ rs₂) (admitSt (rs₁ ++ rs₂) D₁)).derived ↔
      Deriv (rs₁ ++ rs₂) x := by
  have h1 : x ∈ (go fuel (rs₁ ++ rs₂) (seedSt (rs₁ ++ rs₂) D₁)).derived ↔
      DerivFrom (rs₁ ++ rs₂) D₁ x :=
    worklist_eq hb hD₁nd hDb hrb hfuel
  refine h1.trans ?_
  constructor
  · intro hx
    exact derivFrom_append_of_seed hD hx
  · intro hx
    exact derivFrom_mono_seed (fun y hy => by simp at hy) hx

/-- Carried entries survive admission: an old rule's pending
    entry in the admitted state is the very entry the carried
    state held, because both are the distinct-premise filter
    against the same carried derived set. -/
theorem admit_old_entries {rs₁ rs₂ : List Rule} {D₁ : List Nat}
    {pend₁ : List (List Nat)} (hpend : PendOk D₁ rs₁ pend₁)
    {r : Rule} {ps : List Nat} (hr : r ∈ rs₁) (hp : Paired rs₁ pend₁ r ps) :
    Paired (rs₁ ++ rs₂) (admitSt (rs₁ ++ rs₂) D₁).pending r ps := by
  have h1 : ps = (distinct r.premises).filter (fun p => p ∉ D₁) :=
    pendOk_paired hpend hp
  have h2 : PendOk D₁ (rs₁ ++ rs₂) (admitSt (rs₁ ++ rs₂) D₁).pending :=
    pendOk_seed
  obtain ⟨ps', hp'⟩ := paired_of_mem (pend_length h2) (List.mem_append_left rs₂ hr)
  have h3 : ps' = (distinct r.premises).filter (fun p => p ∉ D₁) :=
    pendOk_paired h2 hp'
  have h4 : ps' = ps := h3.trans h1.symm
  rw [h4] at hp'
  exact hp'

/-- The candidate layer's admitted rules: qualified records only,
    premises are the record's links, head is the record's term. -/
def ruleOf (r : Candidate.Record) : Rule := ⟨r.entry.links, r.entry.term⟩

def admitted (rs : List Candidate.Record) : List Rule :=
  (rs.filter Candidate.qualified).map ruleOf

theorem admitted_edge {rs : List Candidate.Record} {ps : List Nat} {a : Nat} :
    edgeOf (admitted rs) ps a ↔
      ∃ r, r ∈ rs ∧ Candidate.qualified r = true ∧
        r.entry.links = ps ∧ r.entry.term = a := by
  constructor
  · rintro ⟨r, hr, hps, ha⟩
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    rw [List.mem_filter] at hr₀
    exact ⟨r₀, hr₀.1, hr₀.2, hps, ha⟩
  · rintro ⟨r, hr, hq, hps, ha⟩
    exact ⟨ruleOf r, List.mem_map.mpr
      ⟨r, List.mem_filter.mpr ⟨hr, hq⟩, rfl⟩, hps, ha⟩

/-- The filtered view: the worklist over the admitted records is
    exactly the least closure of the admitted rules; a
    disqualified record contributes no rule and no derivation. -/
theorem filtered_view_eq {rs : List Candidate.Record} {bound : List Nat}
    (hb : bound.Nodup)
    (hrb : ∀ r ∈ admitted rs, r.head ∈ bound)
    {fuel : Nat} (hfuel : bound.length ≤ fuel) {x : Nat} :
    x ∈ (go fuel (admitted rs) (seedSt (admitted rs) [])).derived ↔
      Deriv (admitted rs) x :=
  worklist_closure hb hrb hfuel

/- Standing controls. -/

/-- The refuted counting form, in miniature: a count that starts
    at the premise list's length and drops by one per processed
    term never reaches zero for a duplicated premise, although
    every premise is processed. The distinct count of the same
    rule against the same processed set is zero. -/
def badRemain (ps : List Nat) (visits : List Nat) : Nat := ps.length - visits.length

theorem control_dup_count :
    badRemain [0, 0] [0] = 1 ∧ (∀ p ∈ [0, 0], p ∈ [0]) ∧
      (distinct [0, 0]).filter (fun p => p ∉ [0]) = [] := by
  refine ⟨rfl, ?_, by decide⟩
  intro p hp
  simp at hp
  simp [hp]

def dupRules : List Rule := [⟨[0, 0], 1⟩, ⟨[], 0⟩]

theorem control_dup_closure :
    (go 10 dupRules (seedSt dupRules [])).derived = [0, 1] := by decide

theorem control_dup_deriv :
    Deriv dupRules 0 ∧ Deriv dupRules 1 ∧ ¬ Deriv dupRules 2 := by
  refine ⟨?_, ?_, ?_⟩
  · refine DerivFrom.fire (r := ⟨[], 0⟩) (by decide) ?_
    intro p hp
    simp at hp
  · refine DerivFrom.fire (r := ⟨[0, 0], 1⟩) (by decide) ?_
    intro p hp
    have hp0 : p = 0 := by simpa using hp
    rw [hp0]
    refine DerivFrom.fire (r := ⟨[], 0⟩) (by decide) ?_
    intro q hq
    simp at hq
  · intro h
    have h2 := derivFrom_least (rs := dupRules) (s := ([] : List Nat))
      (P := fun y => y ∈ [0, 1])
      (fun y hy => by simp at hy)
      (fun r hr hprem => by
        rcases List.mem_cons.mp hr with rfl | hr
        · show (1 : Nat) ∈ [0, 1]
          decide
        · rcases List.mem_singleton.mp hr with rfl
          show (0 : Nat) ∈ [0, 1]
          decide) h
    simp at h2

def goodRec : Candidate.Record where
  entry := ⟨0, [], []⟩
  score := ⟨0, 0, 0, 0, 0, 0⟩
  seen := true
  wanted := true

def badRec : Candidate.Record where
  entry := ⟨1, [], [0]⟩
  score := ⟨0, 0, 0, 0, 0, 0⟩
  seen := false
  wanted := true

/-- A disqualified record changes no derivation: with the bad
    record filtered out, its head is underivable; admitting the
    same rule by hand derives it. -/
theorem control_disqualified :
    admitted [goodRec, badRec] = [⟨[], 0⟩] ∧
      Deriv (admitted [goodRec, badRec]) 0 ∧
      ¬ Deriv (admitted [goodRec, badRec]) 1 ∧
      Deriv [⟨[], 0⟩, ⟨[0], 1⟩] 1 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · refine DerivFrom.fire (r := ⟨[], 0⟩) (by decide) ?_
    intro p hp
    simp at hp
  · intro h
    have h2 := derivFrom_least (rs := admitted [goodRec, badRec])
      (s := ([] : List Nat)) (P := fun y => y = 0)
      (fun y hy => by simp at hy)
      (fun r hr hprem => by
        have h3 : admitted [goodRec, badRec] = [⟨[], 0⟩] := by decide
        rw [h3] at hr
        have hr' : r = ⟨[], 0⟩ := List.mem_singleton.mp hr
        rw [hr']) h
    have hne : (1 : Nat) ≠ 0 := by decide
    exact hne h2
  · refine DerivFrom.fire (r := ⟨[0], 1⟩) (by decide) ?_
    intro p hp
    simp at hp
    rw [hp]
    refine DerivFrom.fire (r := ⟨[], 0⟩) (by decide) ?_
    intro q hq
    simp at hq

#print axioms worklist_eq
#print axioms worklist_closure
#print axioms terminates
#print axioms append_eq
#print axioms admit_old_entries
#print axioms deriv_iff_gderives
#print axioms edgeOf_map
#print axioms filtered_view_eq
#print axioms waiters_only
#print axioms control_dup_count
#print axioms control_dup_closure
#print axioms control_dup_deriv
#print axioms control_disqualified

end Worklist
