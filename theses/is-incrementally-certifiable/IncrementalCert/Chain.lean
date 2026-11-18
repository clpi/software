import SoftwareIsComposable

namespace IncrementalCert

open SoftwareIsComposable

def paretoDominates (a b : Nat × Nat) : Prop :=
  a.1 ≤ b.1 ∧ a.2 ≤ b.2 ∧ (a.1 < b.1 ∨ a.2 < b.2)

def pairOf (p : SymbolProfile) : Nat × Nat :=
  match p.costs with
  | a :: b :: _ => (a.hi, b.hi)
  | _ => (0, 0)

def FixedSelectedAxes (chain : List Release) : Prop :=
  ∀ r, r ∈ chain → ∀ p, p ∈ r.symbols → p.id = 0 ∧ p.costs.length = 2

def ValidMeasurements (chain : List Release) : Prop :=
  ∀ r, r ∈ chain → ∀ p, p ∈ r.symbols → ∀ b, b ∈ p.costs → b.lo ≤ b.hi

def BaselineEligible (base : Release) : Prop :=
  base.symbols ≠ [] ∧ ∀ p, p ∈ base.symbols → ∀ b, b ∈ p.costs → b.lo ≤ b.hi

inductive StepAdmitted : List Release → Prop where
  | single (r : Release) : StepAdmitted [r]
  | cons {r s : Release} {rest : List Release}
      (h : ReleaseAdmitted r s) (t : StepAdmitted (s :: rest)) :
      StepAdmitted (r :: s :: rest)

def costOf (r : Release) : Nat × Nat :=
  match r.symbols with
  | p :: _ => pairOf p
  | [] => (0, 0)

theorem both_hi_le {a b : SymbolProfile} {x y u v : Bounds}
    (h : SymbolAdmitted a b) (ha : a.costs = [x, y]) (hb : b.costs = [u, v]) :
    u.hi ≤ x.hi ∧ v.hi ≤ y.hi := by
  have h0 : (x, u) ∈ a.costs.zip b.costs := by simp [ha, hb]
  have h1 : (y, v) ∈ a.costs.zip b.costs := by simp [ha, hb]
  exact ⟨h.costHi (x, u) h0, h.costHi (y, v) h1⟩

theorem release_hi_le {a b : Release} {pa pb : SymbolProfile}
    {x y u v : Bounds}
    (h : ReleaseAdmitted a b)
    (ha : a.symbols = [pa]) (hb : b.symbols = [pb])
    (hca : pa.costs = [x, y]) (hcb : pb.costs = [u, v])
    (hid : pa.id = pb.id) :
    u.hi ≤ x.hi ∧ v.hi ≤ y.hi := by
  have hmem : pa ∈ a.symbols := by simp [ha]
  have had := h pa hmem
  have hfind : b.symbols.find? (fun q => q.id == pa.id) = some pb := by
    simp [hb, hid, beq_iff_eq]
  simp [hfind] at had
  exact both_hi_le had hca hcb

theorem not_dominates_of_le {earlier later : Nat × Nat}
    (ht : later.1 ≤ earlier.1) (hc : later.2 ≤ earlier.2) :
    ¬ paretoDominates earlier later := by
  intro h
  rcases h with ⟨h1, h2, hstrict⟩
  have he1 : earlier.1 = later.1 := Nat.le_antisymm h1 ht
  have he2 : earlier.2 = later.2 := Nat.le_antisymm h2 hc
  rcases hstrict with hs | hs
  · omega
  · omega

theorem chain_nonempty {chain : List Release} (h : StepAdmitted chain) : chain ≠ [] := by
  cases h <;> simp

theorem pareto_monotone_chain {a b c : Release} {pa pb pc : SymbolProfile}
    {ax ay bx byy cx cy : Bounds}
    (hAB : ReleaseAdmitted a b) (hBC : ReleaseAdmitted b c)
    (hA : FixedSelectedAxes [a, b, c]) (hV : ValidMeasurements [a, b, c])
    (hB : BaselineEligible a)
    (ha : a.symbols = [pa]) (hb : b.symbols = [pb]) (hc : c.symbols = [pc])
    (hca : pa.costs = [ax, ay]) (hcb : pb.costs = [bx, byy]) (hcc : pc.costs = [cx, cy])
    (hid : pa.id = pb.id ∧ pb.id = pc.id) :
    ¬ paretoDominates (ax.hi, ay.hi) (bx.hi, byy.hi) ∧
      ¬ paretoDominates (bx.hi, byy.hi) (cx.hi, cy.hi) ∧
      ¬ paretoDominates (ax.hi, ay.hi) (cx.hi, cy.hi) ∧
      pa.id = 0 ∧ ax.lo ≤ ax.hi ∧ a.symbols ≠ [] := by
  have hshape := hA a (by simp) pa (by simp [ha])
  have hmeas := hV a (by simp) pa (by simp [ha]) ax (by simp [hca])
  have hleAB := release_hi_le hAB ha hb hca hcb hid.1
  have hleBC := release_hi_le hBC hb hc hcb hcc hid.2
  have hmem : pa ∈ a.symbols := by simp [ha]
  have hab := hAB pa hmem
  have hfindb : b.symbols.find? (fun q => q.id == pa.id) = some pb := by
    simp [hb, hid.1, beq_iff_eq]
  simp [hfindb] at hab
  have hmemB : pb ∈ b.symbols := by simp [hb]
  have hbc := hBC pb hmemB
  have hfindc : c.symbols.find? (fun q => q.id == pb.id) = some pc := by
    simp [hc, hid.2, beq_iff_eq]
  simp [hfindc] at hbc
  have hac := symbolAdmitted_trans hab hbc
  have hleAC := both_hi_le hac hca hcc
  exact ⟨not_dominates_of_le hleAB.1 hleAB.2,
    not_dominates_of_le hleBC.1 hleBC.2,
    not_dominates_of_le hleAC.1 hleAC.2,
    hshape.1, hmeas, hB.1⟩

def axesOf : List Nat → List Bounds → List Bounds → Bool
  | [], _, _ => true
  | i :: is, old, new =>
    match old[i]?, new[i]? with
    | some a, some b => decide (b.hi ≤ a.hi) && axesOf is old new
    | _, _ => false

theorem axes_change_hides_regression :
    symbolAdmitted
      { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 10 }, { lo := 0, hi := 1 }] }
      { id := 0, behaviors := [1], costs := [{ lo := 0, hi := 9 }, { lo := 0, hi := 100 }] } = false ∧
    axesOf [0]
      [{ lo := 0, hi := 10 }, { lo := 0, hi := 1 }]
      [{ lo := 0, hi := 9 }, { lo := 0, hi := 100 }] = true ∧
    axesOf [0, 1]
      [{ lo := 0, hi := 10 }, { lo := 0, hi := 1 }]
      [{ lo := 0, hi := 9 }, { lo := 0, hi := 100 }] = false := by
  decide

theorem not_per_execution :
    ¬ ∀ x y : Nat, (1 ≤ x ∧ x ≤ 100) → (2 ≤ y ∧ y ≤ 3) → y ≤ x :=
  SoftwareIsComposable.not_per_execution

end IncrementalCert
