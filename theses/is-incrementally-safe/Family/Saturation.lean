/-!
# S-01: saturation is deterministic, whatever the merge order

The proposal says the space is reached by deterministic equality saturation with
premise-tracked merges. The repos prove Horn closure (`close_exact`, `WorklistClosure`), but not
that saturation by single rule firings in an arbitrary order is deterministic, and nothing ties
merges to equalities. This module proves both for any finite Horn system:

* `run_sound`: every fact added by any firing order is derivable from the premises.
* `saturated_exact`: any firing order that ends saturated holds exactly the derivable facts.
* `saturation_deterministic`: so any two saturating orders agree.
* `EqRules` encodes equality saturation over a finite set of terms (reflexivity, symmetry,
  transitivity, congruence for a table of unary operations, plus premise equalities) as such a
  system. `eq_deterministic` instantiates the result: the merged classes do not depend on merge
  order.
* `Derives` is the premise tracking: each merge is a derivation tree whose leaves are premise
  equalities, and adding premises never undoes a merge (`derives_mono`).

Out of scope: the e-graph data structure itself (hash-consing, union-find, rebuilding) and
n-ary congruence; this is the specification such an implementation would refine.

Prior art: chaotic iteration and order-independence of least fixed points (Cousot and Cousot
1977); congruence closure (Nelson and Oppen 1980; Downey, Sethi and Tarjan 1980); equality
saturation (Tate et al. 2009; egg, Willsey et al. 2021). Not new.
-/
namespace Family.Saturation

variable {F : Type}

/-- Least model of Horn rules over a set of premise facts. -/
inductive Derives (base : F → Prop) (rules : List (List F × F)) : F → Prop where
  | base {x} : base x → Derives base rules x
  | rule {r} : r ∈ rules → (∀ p, p ∈ r.1 → Derives base rules p) → Derives base rules r.2

/-- One firing: add a rule's conclusion when its premises are present. -/
inductive Fires (rules : List (List F × F)) : List F → List F → Prop where
  | fire {S r} : r ∈ rules → (∀ p, p ∈ r.1 → p ∈ S) → Fires rules S (r.2 :: S)

/-- Any finite sequence of firings. -/
inductive Run (rules : List (List F × F)) : List F → List F → Prop where
  | done (S) : Run rules S S
  | step {S S' T} : Fires rules S S' → Run rules S' T → Run rules S T

def Saturated (rules : List (List F × F)) (S : List F) : Prop :=
  ∀ r, r ∈ rules → (∀ p, p ∈ r.1 → p ∈ S) → r.2 ∈ S

theorem run_sound {base : F → Prop} {rules : List (List F × F)} {S T : List F}
    (h : Run rules S T) (hS : ∀ x, x ∈ S → Derives base rules x) :
    ∀ x, x ∈ T → Derives base rules x := by
  induction h with
  | done => exact hS
  | step hf _ ih =>
    apply ih
    cases hf with
    | fire hr hp =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact .rule hr (fun p hp' => hS p (hp p hp'))
      · exact hS x hx

theorem run_mono {rules : List (List F × F)} {S T : List F} (h : Run rules S T) :
    ∀ x, x ∈ S → x ∈ T := by
  induction h with
  | done => exact fun _ h => h
  | step hf _ ih =>
    cases hf with
    | fire _ _ => exact fun x hx => ih x (List.mem_cons_of_mem _ hx)

theorem saturated_exact {base : F → Prop} {rules : List (List F × F)} {S T : List F}
    (hS : ∀ x, x ∈ S ↔ base x) (h : Run rules S T) (hsat : Saturated rules T) (x : F) :
    x ∈ T ↔ Derives base rules x := by
  constructor
  · exact run_sound h (fun y hy => .base ((hS y).mp hy)) x
  · intro hd
    induction hd with
    | base hb => exact run_mono h _ ((hS _).mpr hb)
    | rule hr _ ih => exact hsat _ hr ih

theorem saturation_deterministic {base : F → Prop} {rules : List (List F × F)}
    {S T T' : List F} (hS : ∀ x, x ∈ S ↔ base x) (h : Run rules S T) (h' : Run rules S T')
    (hsat : Saturated rules T) (hsat' : Saturated rules T') (x : F) : x ∈ T ↔ x ∈ T' :=
  (saturated_exact hS h hsat x).trans (saturated_exact hS h' hsat' x).symm

theorem derives_mono {base base' : F → Prop} {rules : List (List F × F)}
    (hb : ∀ x, base x → base' x) {x : F} (h : Derives base rules x) : Derives base' rules x := by
  induction h with
  | base h => exact .base (hb _ h)
  | rule hr _ ih => exact .rule hr ih

/-! ## Equality saturation over a finite set of terms -/

variable {T : Type}

/-- Rules for equality over the listed terms: reflexivity, symmetry, transitivity, and
congruence for each unary operation in `ops` (an operation maps a term to its application). -/
def EqRules (terms : List T) (ops : List (T → T)) : List (List (T × T) × (T × T)) :=
  terms.map (fun t => ([], (t, t))) ++
  (terms.flatMap fun a => terms.map fun b => ([(a, b)], (b, a))) ++
  (terms.flatMap fun a => terms.flatMap fun b => terms.map fun c => ([(a, b), (b, c)], (a, c))) ++
  (ops.flatMap fun f => terms.flatMap fun a => terms.map fun b => ([(a, b)], (f a, f b)))

theorem eq_deterministic (terms : List T) (ops : List (T → T)) (prem : (T × T) → Prop)
    {S M M' : List (T × T)} (hS : ∀ x, x ∈ S ↔ prem x)
    (h : Run (EqRules terms ops) S M) (h' : Run (EqRules terms ops) S M')
    (hsat : Saturated (EqRules terms ops) M) (hsat' : Saturated (EqRules terms ops) M')
    (a b : T) : (a, b) ∈ M ↔ (a, b) ∈ M' :=
  saturation_deterministic hS h h' hsat hsat' (a, b)

/-- A merge in a saturated state is symmetric, as an equivalence should be. -/
theorem eq_symm (terms : List T) (ops : List (T → T)) {M : List (T × T)}
    (hsat : Saturated (EqRules terms ops) M) {a b : T} (ha : a ∈ terms) (hb : b ∈ terms)
    (h : (a, b) ∈ M) : (b, a) ∈ M := by
  apply hsat ([(a, b)], (b, a)) _ (fun p hp => by simp at hp; subst hp; exact h)
  simp only [EqRules, List.mem_append, List.mem_flatMap, List.mem_map]
  left; left; right
  exact ⟨a, ha, b, hb, rfl⟩

end Family.Saturation
