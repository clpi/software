namespace SoftwareIsComposable

structure Profile (ω : Type) where
  obs : ω → Prop

def profileLE {ω : Type} (p q : Profile ω) : Prop :=
  ∀ o, p.obs o → q.obs o

theorem profileLE_refl {ω : Type} (p : Profile ω) : profileLE p p :=
  fun _ h => h

theorem profileLE_trans {ω : Type} {p q r : Profile ω}
    (hpq : profileLE p q) (hqr : profileLE q r) : profileLE p r :=
  fun o h => hqr o (hpq o h)

theorem profileLE_antisymm {ω : Type} {p q : Profile ω}
    (hpq : profileLE p q) (hqp : profileLE q p) : p = q := by
  cases p
  cases q
  apply congrArg Profile.mk
  funext o
  exact propext ⟨hpq o, hqp o⟩

structure Release (σ ω : Type) where
  behavior : σ → Profile ω

def releaseLE {σ ω : Type} (R S : Release σ ω) : Prop :=
  ∀ s, profileLE (R.behavior s) (S.behavior s)

theorem releaseLE_refl {σ ω : Type} (R : Release σ ω) : releaseLE R R :=
  fun _ => profileLE_refl _

theorem releaseLE_trans {σ ω : Type} {R S T : Release σ ω}
    (hRS : releaseLE R S) (hST : releaseLE S T) : releaseLE R T :=
  fun s => profileLE_trans (hRS s) (hST s)

structure Delta (σ ω : Type) where
  changed : σ → Bool
  update : σ → Profile ω
  inspect : σ → Bool

def apply {σ ω : Type} (R : Release σ ω) (d : Delta σ ω) : Release σ ω where
  behavior s := if d.changed s then d.update s else R.behavior s

theorem apply_changed {σ ω : Type} (R : Release σ ω) (d : Delta σ ω) {s : σ}
    (h : d.changed s = true) : (apply R d).behavior s = d.update s := by
  simp [apply, h]

theorem apply_unchanged {σ ω : Type} (R : Release σ ω) (d : Delta σ ω) {s : σ}
    (h : d.changed s = false) : (apply R d).behavior s = R.behavior s := by
  simp [apply, h]

theorem incremental_monotone {σ ω : Type} (R : Release σ ω) (d : Delta σ ω)
    (h : ∀ s, d.changed s = true → profileLE (d.update s) (R.behavior s)) :
    releaseLE (apply R d) R := by
  intro s
  cases hchg : d.changed s with
  | true =>
    rw [apply_changed R d hchg]
    exact h s hchg
  | false =>
    rw [apply_unchanged R d hchg]
    exact profileLE_refl _

inductive Cone {σ : Type} (deps : σ → σ → Prop) (changed : σ → Bool) : σ → Prop where
  | root {s : σ} : changed s = true → Cone deps changed s
  | step {s t : σ} : deps s t → Cone deps changed t → Cone deps changed s

theorem cone_of_changed {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool} {s : σ}
    (h : changed s = true) : Cone deps changed s :=
  Cone.root h

theorem not_cone_not_changed {σ : Type} {deps : σ → σ → Prop} {changed : σ → Bool} {s : σ}
    (h : ¬ Cone deps changed s) : changed s = false := by
  cases hchg : changed s with
  | false => rfl
  | true => exact (h (Cone.root hchg)).elim

inductive Reaches {σ ω : Type} (deps : σ → σ → Prop) (B : σ → Profile ω) : σ → ω → Prop where
  | here {s : σ} {o : ω} : (B s).obs o → Reaches deps B s o
  | step {s t : σ} {o : ω} : deps s t → Reaches deps B t o → Reaches deps B s o

theorem reaches_transfer
    {σ ω : Type} {deps : σ → σ → Prop} {changed : σ → Bool}
    {B B' : σ → Profile ω}
    (hagree : ∀ s, changed s = false → B' s = B s)
    {s : σ} {o : ω} (h : Reaches deps B' s o) (hout : ¬ Cone deps changed s) :
    Reaches deps B s o :=
  Reaches.rec
    (motive := fun s o _ => ¬ Cone deps changed s → Reaches deps B s o)
    (fun {s o} hobs hout => by
      rw [hagree s (not_cone_not_changed hout)] at hobs
      exact Reaches.here hobs)
    (fun {s t o} hdep _ ih hout =>
      Reaches.step hdep (ih (fun ht => hout (Cone.step hdep ht))))
    h hout

theorem reaches_outside_stable
    {σ ω : Type} {deps : σ → σ → Prop} {changed : σ → Bool}
    {B B' : σ → Profile ω}
    (hagree : ∀ s, changed s = false → B' s = B s)
    {s : σ} {o : ω} (hout : ¬ Cone deps changed s) :
    Reaches deps B' s o ↔ Reaches deps B s o :=
  ⟨fun h => reaches_transfer hagree h hout,
    fun h => reaches_transfer (fun t ht => (hagree t ht).symm) h hout⟩

theorem reaches_monotone
    {σ ω : Type} {deps : σ → σ → Prop} {B B' : σ → Profile ω}
    (hle : ∀ s, profileLE (B' s) (B s))
    {s : σ} {o : ω} (h : Reaches deps B' s o) : Reaches deps B s o :=
  Reaches.rec
    (motive := fun s o _ => Reaches deps B s o)
    (fun {s o} hobs => Reaches.here (hle s o hobs))
    (fun {_ _ _} hdep _ ih => Reaches.step hdep ih)
    h

structure ProfileOrderExport (ω : Type) where
  le : Profile ω → Profile ω → Prop
  refl : ∀ p, le p p
  trans : ∀ p q r, le p q → le q r → le p r
  antisymm : ∀ p q, le p q → le q p → p = q

def canonicalProfileOrder {ω : Type} : ProfileOrderExport ω where
  le := profileLE
  refl := profileLE_refl
  trans := fun _ _ _ => profileLE_trans
  antisymm := fun _ _ => profileLE_antisymm

theorem equivalence_obligation_profileOrder {ω : Type} (p q : Profile ω) :
    canonicalProfileOrder.le p q ↔ profileLE p q := Iff.rfl

theorem equivalence_obligation_incremental
    {σ ω : Type} (R : Release σ ω) (d : Delta σ ω)
    (h : ∀ s, d.changed s = true → canonicalProfileOrder.le (d.update s) (R.behavior s)) :
    releaseLE (apply R d) R :=
  incremental_monotone R d h

def idDelta {σ ω : Type} : Delta σ ω where
  changed _ := false
  update _ := ⟨fun _ => False⟩
  inspect _ := false

theorem apply_idDelta {σ ω : Type} (R : Release σ ω) : apply R idDelta = R := by
  simp [apply, idDelta]

def compose {σ ω : Type} (d1 d2 : Delta σ ω) : Delta σ ω where
  changed s := d1.changed s || d2.changed s
  update s := if d2.changed s then d2.update s else d1.update s
  inspect s := d1.inspect s || d2.inspect s

theorem apply_apply_eq_compose {σ ω : Type} (R : Release σ ω) (d1 d2 : Delta σ ω) :
    apply (apply R d1) d2 = apply R (compose d1 d2) := by
  simp only [apply, compose]
  congr 1
  funext s
  cases h2 : d2.changed s <;> cases h1 : d1.changed s <;> simp [h1, h2]

def foldApply {σ ω : Type} (R : Release σ ω) : List (Delta σ ω) → Release σ ω
  | [] => R
  | d :: ds => foldApply (apply R d) ds

def composeAll {σ ω : Type} : List (Delta σ ω) → Delta σ ω
  | [] => idDelta
  | d :: ds => compose d (composeAll ds)

theorem foldApply_eq_composeAll {σ ω : Type} (R : Release σ ω) (ds : List (Delta σ ω)) :
    foldApply R ds = apply R (composeAll ds) := by
  induction ds generalizing R with
  | nil =>
    simp [foldApply, composeAll, apply_idDelta]
  | cons d ds ih =>
    rw [foldApply, ih, apply_apply_eq_compose]
    rfl

end SoftwareIsComposable
