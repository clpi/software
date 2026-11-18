import SoftwareDoesntRegress.Gate
import SoftwareIsComposable.Admission

namespace SoftwareDoesntRegress

structure BaselineStaysEligible {A : Type} (eligible : A → Bool) (baseline : A) : Prop where
  holds : eligible baseline = true

structure AxesRight {I : Type} (authorized selected : List I) : Prop where
  intoAuthorized : ∀ i, i ∈ selected → i ∈ authorized
  intoSelected : ∀ i, i ∈ authorized → i ∈ selected

structure MeasurementsValid {A : Type} (bounds : A → Nat → Bound) (axes : List Nat)
    (baseline : A) : Prop where
  consistent : ∀ i, i ∈ axes → (bounds baseline i).lo ≤ (bounds baseline i).hi

def guardBool {A : Type} (eligible : A → Bool) (axes : List Nat) (bounds : A → Nat → Bound)
    (baseline x : A) : Bool :=
  eligible x &&
    axes.all fun i =>
      Bound.ok (bounds x i) && Bound.ok (bounds baseline i) &&
        decide ((bounds x i).hi ≤ (bounds baseline i).hi)

def select {A : Type} (candidates : List A) (eligible : A → Bool) (axes : List Nat)
    (bounds : A → Nat → Bound) (baseline : A) : A :=
  match candidates.filter (guardBool eligible axes bounds baseline) with
  | [] => baseline
  | x :: _ => x

theorem behaviorsKept_eq_composable (a b : List Nat) :
    behaviorsKept a b = SoftwareIsComposable.accepts a b := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    simp [behaviorsKept, SoftwareIsQuantifiable.Pareto.accepts, SoftwareIsComposable.accepts,
      List.all_cons, ih]

theorem composable_hi_of_boundsNoWorse {inc cand : List Bound}
    (h : boundsNoWorse inc cand = true) {a b : Bound} (hx : (a, b) ∈ inc.zip cand) :
    b.hi ≤ a.hi := by
  induction inc generalizing cand with
  | nil => simp at hx
  | cons i is ih =>
    cases cand with
    | nil => simp [boundsNoWorse] at h
    | cons c cs =>
      rw [boundsNoWorse] at h
      have h' := band_eq.mp h
      rw [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with heq | hx
      · have ha : a = i := congrArg Prod.fst heq
        have hb : b = c := congrArg Prod.snd heq
        subst ha
        subst hb
        exact (Bound.noWorse_iff.mp h'.1).2
      · exact ih h'.2 hx

theorem axes_baseline_ok {A : Type} (bounds : A → Nat → Bound) (baseline : A) :
    ∀ xs, (∀ i, i ∈ xs → (bounds baseline i).lo ≤ (bounds baseline i).hi) →
      List.all xs (fun i =>
        Bound.ok (bounds baseline i) && Bound.ok (bounds baseline i) &&
          decide ((bounds baseline i).hi ≤ (bounds baseline i).hi)) = true
  | [], _ => rfl
  | i :: is, h => by
    rw [List.all_cons, band_eq]
    refine And.intro ?_ (axes_baseline_ok bounds baseline is
      (fun j hj => h j (List.mem_cons_of_mem i hj)))
    have hc := h i (List.mem_cons.mpr (Or.inl rfl))
    simp [Bound.ok, decide_eq_true_eq, hc]

theorem baseline_guard {A : Type} {eligible : A → Bool} {axes : List Nat}
    {bounds : A → Nat → Bound} {baseline : A}
    (hB : BaselineStaysEligible eligible baseline)
    (hM : MeasurementsValid bounds axes baseline) :
    guardBool eligible axes bounds baseline baseline = true := by
  unfold guardBool
  rw [hB.holds, Bool.true_and]
  exact axes_baseline_ok bounds baseline axes hM.consistent

theorem baseline_is_witness {A : Type} {eligible : A → Bool} {authorized selected : List Nat}
    {bounds : A → Nat → Bound} {baseline : A}
    (hB : BaselineStaysEligible eligible baseline)
    (hA : AxesRight authorized selected)
    (hM : MeasurementsValid bounds selected baseline) :
    guardBool eligible selected bounds baseline baseline = true ∧
      ∀ i, i ∈ authorized → (bounds baseline i).hi ≤ (bounds baseline i).hi ∧
        (bounds baseline i).lo ≤ (bounds baseline i).hi := by
  refine ⟨baseline_guard hB hM, ?_⟩
  intro i hi
  have hs : i ∈ selected := hA.intoSelected i hi
  exact And.intro (Nat.le_refl _) (hM.consistent i hs)

theorem filter_head_guard {A : Type} {p : A → Bool} {x : A} {xs ys : List A}
    (h : xs.filter p = x :: ys) : p x = true := by
  have hx : x ∈ xs.filter p := by simp [h]
  exact (List.mem_filter.mp hx).2

theorem select_never_regresses {A : Type} {eligible : A → Bool} {authorized selected : List Nat}
    {bounds : A → Nat → Bound} {baseline : A} {candidates : List A}
    (hB : BaselineStaysEligible eligible baseline)
    (hA : AxesRight authorized selected)
    (hM : MeasurementsValid bounds selected baseline)
    (x : A) (hsel : x = select candidates eligible selected bounds baseline) :
    ∀ i, i ∈ authorized →
      (bounds x i).hi ≤ (bounds baseline i).hi ∧
        (bounds baseline i).lo ≤ (bounds baseline i).hi ∧
        eligible baseline = true := by
  intro i hi
  have hs : i ∈ selected := hA.intoSelected i hi
  subst hsel
  cases hfilter : candidates.filter (guardBool eligible selected bounds baseline) with
  | nil =>
    rw [select, hfilter]
    refine And.intro (Nat.le_refl _) (And.intro (hM.consistent i hs) hB.holds)
  | cons y ys =>
    have hg := filter_head_guard hfilter
    rw [select, hfilter]
    simp [guardBool, band_eq, List.all_eq_true, decide_eq_true_eq] at hg
    refine And.intro (hg.2 i hs).2 (And.intro (hM.consistent i hs) hB.holds)

theorem select_keeps_baseline_available {A : Type} {eligible : A → Bool}
    {selected : List Nat} {bounds : A → Nat → Bound} {baseline : A} {candidates : List A}
    (hB : BaselineStaysEligible eligible baseline)
    (hM : MeasurementsValid bounds selected baseline)
    (hb : baseline ∈ candidates) :
    baseline ∈ candidates.filter (guardBool eligible selected bounds baseline) := by
  exact List.mem_filter.mpr ⟨hb, baseline_guard hB hM⟩

end SoftwareDoesntRegress
