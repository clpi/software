import ReviewProofs

namespace ReviewStatement

/-- Only the declared admission and frontier observations must factor through
the relevant slice. Receipt identity and other unobserved data may differ. -/
def RespectsDecisions {A : Type} (relevant : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject) : Prop :=
  ∀ X Y : A → Prop, SameRelevant relevant X Y →
    SameDecisions k catalogue project X Y

theorem respects_decisions_of_respects_relevant {A : Type}
    (relevant : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject)
    (h : RespectsRelevant relevant project) :
    RespectsDecisions relevant project k catalogue := by
  intro X Y same
  have hp := h X Y same
  exact ⟨fun s => congrArg (fun f => ScopedFrontier.admitted k s (f s)) hp,
    congrArg (ScopedFrontier.select k catalogue) hp⟩

/-- A falsifier inside the declared technical model. Fidelity and process
permission remain separate application premises. -/
def LoadBearingWitness {A : Type} (relevant : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject)
    (X Y : A → Prop) : Prop :=
  (∃ a, relevant a ∧ ((X a ∧ ¬ Y a) ∨ (Y a ∧ ¬ X a))) ∨
  (∃ s, ScopedFrontier.admitted k s (project X s) ≠
    ScopedFrontier.admitted k s (project Y s)) ∨
  ScopedFrontier.select k catalogue (project X) ≠
    ScopedFrontier.select k catalogue (project Y)

theorem redundancy_iff_no_load_bearing_witness {A : Type}
    (relevant : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject)
    (X Y : A → Prop) :
    (SameRelevant relevant X Y ∧ SameDecisions k catalogue project X Y) ↔
      ¬ LoadBearingWitness relevant project k catalogue X Y := by
  classical
  constructor
  · rintro ⟨same, decisions⟩ (⟨a, ha, change⟩ | ⟨s, change⟩ | change)
    · rcases change with ⟨hx, hn⟩ | ⟨hy, hn⟩
      · exact hn ((same a ha).mp hx)
      · exact hn ((same a ha).mpr hy)
    · exact change (decisions.1 s)
    · exact change decisions.2
  · intro absent
    constructor
    · intro a ha
      constructor
      · intro hx
        apply Classical.byContradiction
        intro hy
        exact absent (Or.inl ⟨a, ha, Or.inl ⟨hx, hy⟩⟩)
      · intro hy
        apply Classical.byContradiction
        intro hx
        exact absent (Or.inl ⟨a, ha, Or.inr ⟨hy, hx⟩⟩)
    · constructor
      · intro s
        apply Classical.byContradiction
        intro change
        exact absent (Or.inr (Or.inl ⟨s, change⟩))
      · apply Classical.byContradiction
        intro change
        exact absent (Or.inr (Or.inr change))

theorem prospective_iff_no_load_bearing_outcome {A Outcome : Type}
    (allowed : Outcome → Prop) (relevant : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject)
    (X : A → Prop) (Y : Outcome → A → Prop) :
    (∀ o, allowed o → SameRelevant relevant X (Y o) ∧
      SameDecisions k catalogue project X (Y o)) ↔
    ¬ ∃ o, allowed o ∧ LoadBearingWitness relevant project k catalogue X (Y o) := by
  constructor
  · rintro all ⟨o, ho, witness⟩
    exact (redundancy_iff_no_load_bearing_witness relevant project k catalogue X
      (Y o)).mp (all o ho) witness
  · intro absent o ho
    apply (redundancy_iff_no_load_bearing_witness relevant project k catalogue X (Y o)).mpr
    intro witness
    exact absent ⟨o, ho, witness⟩

/-- The algebraic core needs no invented objectives or successful release.
It preserves the relevant truth of every post-review derivation, even if
post-review rules are unsound outside the relevant slice. -/
theorem prospective_omission {A Outcome : Type}
    (B₀ : A → Prop) (R₀ : List A → A → Prop)
    (B₁ : Outcome → A → Prop) (R₁ : Outcome → List A → A → Prop)
    (allowed : Outcome → Prop) (relevant TrueAt : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject)
    (valid_roots : ∀ a, B₀ a → TrueAt a)
    (valid_rules : Qualification.Closed R₀ TrueAt)
    (projection_respects : RespectsDecisions relevant project k catalogue)
    (all_outcomes_conservative : ∀ o, allowed o →
      SameRelevant relevant (Q B₀ R₀) (Q (B₁ o) (R₁ o))) :
    (∀ a, Q B₀ R₀ a → TrueAt a) ∧
    (∀ o, allowed o →
      SameRelevant relevant (Q B₀ R₀) (Q (B₁ o) (R₁ o)) ∧
      SameDecisions k catalogue project (Q B₀ R₀) (Q (B₁ o) (R₁ o)) ∧
      (∀ a, relevant a → Q (B₁ o) (R₁ o) a → TrueAt a)) := by
  have sound := Qualification.soundness valid_roots valid_rules
  refine ⟨sound, ?_⟩
  intro o ho
  have same := all_outcomes_conservative o ho
  exact ⟨same, projection_respects _ _ same,
    fun a ha derived => sound a ((same a ha).mpr derived)⟩

/-- Successful, nonvacuous application: the witnesses are retained in the
conclusion, and every required objective remains derivable and true. -/
theorem review_omission {A Outcome : Type}
    (B₀ : A → Prop) (R₀ : List A → A → Prop)
    (B₁ : Outcome → A → Prop) (R₁ : Outcome → List A → A → Prop)
    (allowed : Outcome → Prop) (relevant required TrueAt : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject)
    (subject : ScopedFrontier.Subject)
    (objectives_exist : ∃ a, required a)
    (outcomes_exist : ∃ o, allowed o)
    (subject_listed : subject ∈ catalogue)
    (baseline_admitted : ScopedFrontier.admitted k subject
      (project (Q B₀ R₀) subject) = true)
    (objectives_relevant : ∀ a, required a → relevant a)
    (objectives_discharged : ∀ a, required a → Q B₀ R₀ a)
    (valid_roots : ∀ a, B₀ a → TrueAt a)
    (valid_rules : Qualification.Closed R₀ TrueAt)
    (projection_respects : RespectsDecisions relevant project k catalogue)
    (all_outcomes_conservative : ∀ o, allowed o →
      SameRelevant relevant (Q B₀ R₀) (Q (B₁ o) (R₁ o))) :
    (∃ a, required a) ∧ (∃ o, allowed o) ∧ subject ∈ catalogue ∧
    ScopedFrontier.admitted k subject (project (Q B₀ R₀) subject) = true ∧
    (∀ a, required a → Q B₀ R₀ a ∧ TrueAt a) ∧
    (∀ o, allowed o →
      SameRelevant relevant (Q B₀ R₀) (Q (B₁ o) (R₁ o)) ∧
      SameDecisions k catalogue project (Q B₀ R₀) (Q (B₁ o) (R₁ o)) ∧
      (∀ a, required a → Q (B₁ o) (R₁ o) a ∧ TrueAt a) ∧
      ScopedFrontier.admitted k subject (project (Q (B₁ o) (R₁ o)) subject) = true) := by
  have core := prospective_omission B₀ R₀ B₁ R₁ allowed relevant TrueAt project
    k catalogue valid_roots valid_rules projection_respects all_outcomes_conservative
  refine ⟨objectives_exist, outcomes_exist, subject_listed, baseline_admitted,
    (fun a ha => ⟨objectives_discharged a ha, core.1 a (objectives_discharged a ha)⟩), ?_⟩
  intro o ho
  have preserved := core.2 o ho
  refine ⟨preserved.1, preserved.2.1, ?_, ?_⟩
  · intro a ha
    have derived := (preserved.1 a (objectives_relevant a ha)).mp
      (objectives_discharged a ha)
    exact ⟨derived, preserved.2.2 a (objectives_relevant a ha) derived⟩
  · exact (preserved.2.1.1 subject).symm.trans baseline_admitted

#print axioms respects_decisions_of_respects_relevant
#print axioms redundancy_iff_no_load_bearing_witness
#print axioms prospective_iff_no_load_bearing_outcome
#print axioms prospective_omission
#print axioms review_omission

end ReviewStatement
