import ReviewStatement

namespace ReviewStatement

/-- A target predicate containing the source roots and closed under the source
    rules contains the entire source qualification closure. This is a sufficient
    certificate; without converse inclusion its rule condition is not necessary. -/
theorem closure_included_of_roots_rules
    {A : Type} {B₀ B₁ : A → Prop} {R₀ R₁ : List A → A → Prop}
    (roots : ∀ a, B₁ a → Q B₀ R₀ a)
    (rules : Qualification.Closed R₁ (Q B₀ R₀)) :
    ∀ a, Q B₁ R₁ a → Q B₀ R₀ a :=
  Qualification.least roots rules

/-- Mutual root/rule absorption exactly characterizes equality of qualification
    closures, allowing both roots and rules to change. -/
theorem basis_conservative_iff
    {A : Type} (B₀ B₁ : A → Prop) (R₀ R₁ : List A → A → Prop) :
    BasisConservative B₀ B₁ R₀ R₁ ↔
      ∀ a, Q B₀ R₀ a ↔ Q B₁ R₁ a := by
  constructor
  · intro h a
    exact ⟨Qualification.least h.2.2.1 h.2.2.2 a,
      Qualification.least h.1 h.2.1 a⟩
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha
      exact (h a).mpr (Qualification.Derives.root ha)
    · intro ps a hr hp
      exact (h a).mpr (Qualification.Derives.step hr (fun p hm => (h p).mp (hp p hm)))
    · intro a ha
      exact (h a).mp (Qualification.Derives.root ha)
    · intro ps a hr hp
      exact (h a).mp (Qualification.Derives.step hr (fun p hm => (h p).mpr (hp p hm)))

/-- F1 at its original public proposition. -/
theorem full_closure_claim : FullClosureClaim := by
  intro A B₀ B₁ R₀ R₁
  exact basis_conservative_iff B₀ B₁ R₀ R₁

/-- For a positive extension, the two obligations in the reverse direction
    follow from the independently established root/rule inclusions. -/
theorem positive_extension_redundant_iff
    {A : Type} (B₀ B₁ : A → Prop) (R₀ R₁ : List A → A → Prop)
    (roots_extend : ∀ a, B₀ a → B₁ a)
    (rules_extend : ∀ ps a, R₀ ps a → R₁ ps a) :
    (∀ a, Q B₀ R₀ a ↔ Q B₁ R₁ a) ↔
      (∀ a, B₁ a → Q B₀ R₀ a) ∧ Qualification.Closed R₁ (Q B₀ R₀) := by
  constructor
  · intro h
    have hb := (basis_conservative_iff B₀ B₁ R₀ R₁).mpr h
    exact ⟨hb.1, hb.2.1⟩
  · intro h a
    exact ⟨Qualification.monotone roots_extend rules_extend a,
      Qualification.least h.1 h.2 a⟩

/-- Positive additions can be checked only at their added roots and rules;
    inherited roots and rules already satisfy the certificate. -/
theorem positive_additions_redundant_iff
    {A : Type} (B V : A → Prop) (R S : List A → A → Prop) :
    (∀ a, Q B R a ↔ Q (fun x => B x ∨ V x) (fun ps x => R ps x ∨ S ps x) a) ↔
      (∀ a, V a → Q B R a) ∧ Qualification.Closed S (Q B R) := by
  have extension := positive_extension_redundant_iff B (fun x => B x ∨ V x)
    R (fun ps x => R ps x ∨ S ps x)
    (fun _ h => Or.inl h) (fun _ _ h => Or.inl h)
  constructor
  · intro h
    have hc := extension.mp h
    exact ⟨fun a ha => hc.1 a (Or.inr ha),
      fun ps a hr hp => hc.2 ps a (Or.inr hr) hp⟩
  · intro h
    apply extension.mpr
    constructor
    · intro a ha
      cases ha with
      | inl hb => exact Qualification.Derives.root hb
      | inr hv => exact h.1 a hv
    · intro ps a hr hp
      cases hr with
      | inl hb => exact Qualification.Derives.step hb hp
      | inr hs => exact h.2 ps a hs hp

/-- With fixed rules, root absorption is both necessary and sufficient. -/
theorem review_roots_redundant_iff
    {A : Type} (B V : A → Prop) (R : List A → A → Prop) :
    (∀ a, Q B R a ↔ Q (fun x => B x ∨ V x) R a) ↔
      ∀ a, V a → Q B R a := by
  constructor
  · intro h a hv
    exact (h a).mpr (Qualification.Derives.root (Or.inr hv))
  · intro h a
    constructor
    · exact Qualification.monotone (fun _ hb => Or.inl hb) (fun _ _ hr => hr) a
    · apply Qualification.least (rules := Qualification.closed B R) ?_ a
      intro x hx
      cases hx with
      | inl hb => exact Qualification.Derives.root hb
      | inr hv => exact h x hv

/-- With fixed roots, an added rule relation is redundant exactly when the
    baseline closure is already closed under it. -/
theorem review_rules_redundant_iff
    {A : Type} (B : A → Prop) (R S : List A → A → Prop) :
    (∀ a, Q B R a ↔ Q B (fun ps x => R ps x ∨ S ps x) a) ↔
      Qualification.Closed S (Q B R) := by
  constructor
  · intro h ps a hr hp
    exact (h a).mpr (Qualification.Derives.step (Or.inr hr)
      (fun p hm => (h p).mp (hp p hm)))
  · intro h a
    constructor
    · exact Qualification.monotone (fun _ hb => hb) (fun _ _ hr => Or.inl hr) a
    · apply Qualification.least (fun _ hb => Qualification.Derives.root hb) ?_ a
      intro ps x hr hp
      cases hr with
      | inl hb => exact Qualification.Derives.step hb hp
      | inr hs => exact h ps x hs hp

/-- The positive-addition characterization lifts uniformly to every declared
    admissible outcome; one checked actual outcome cannot discharge this. -/
theorem uniform_positive_additions_redundant_iff
    {A Outcome : Type} (B : A → Prop) (R : List A → A → Prop)
    (V : Outcome → A → Prop) (S : Outcome → List A → A → Prop)
    (allowed : Outcome → Prop) :
    (∀ o, allowed o → ∀ a,
      Q B R a ↔ Q (fun x => B x ∨ V o x) (fun ps x => R ps x ∨ S o ps x) a) ↔
    (∀ o, allowed o → (∀ a, V o a → Q B R a) ∧
      Qualification.Closed (S o) (Q B R)) := by
  constructor
  · intro h o ho
    exact (positive_additions_redundant_iff B (V o) R (S o)).mp (h o ho)
  · intro h o ho
    exact (positive_additions_redundant_iff B (V o) R (S o)).mpr (h o ho)

/-- Equality of the actual projector outputs transports the existing admission
    and frontier definitions. No alternative frontier is introduced. -/
theorem same_decisions_of_projection_eq
    {A : Type}
    {k : ScopedFrontier.Contract} {catalogue : List ScopedFrontier.Subject}
    {project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input}
    {X Y : A → Prop} (heq : project X = project Y) :
    SameDecisions k catalogue project X Y := by
  constructor
  · intro s
    exact congrArg (fun inputs => ScopedFrontier.admitted k s (inputs s)) heq
  · exact congrArg (ScopedFrontier.select k catalogue) heq

/-- F2 at its original public proposition. -/
theorem relevant_claim : RelevantClaim := by
  intro A B₀ B₁ R₀ R₁ relevant project k catalogue respects same
  exact same_decisions_of_projection_eq (respects (Q B₀ R₀) (Q B₁ R₁) same)

/-- Full closure equality suffices for any fixed projector, without a separate
    relevant-slice invariant. Function/proposition extensionality is explicit
    in the kernel axiom report for this corollary. -/
theorem same_decisions_of_full_closure
    {A : Type}
    (B₀ B₁ : A → Prop) (R₀ R₁ : List A → A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject)
    (same : ∀ a, Q B₀ R₀ a ↔ Q B₁ R₁ a) :
    SameDecisions k catalogue project (Q B₀ R₀) (Q B₁ R₁) := by
  exact same_decisions_of_projection_eq
    (congrArg project (funext (fun a => propext (same a))))

/-- F3 at its original public proposition. The stronger mathematical core is
    separated from application nonvacuity and coverage evidence elsewhere. -/
theorem omission_claim : OmissionClaim := by
  intro A Outcome B₀ R₀ B₁ R₁ allowed relevant required TrueAt project k catalogue subject
    _objectives_exist _outcomes_exist _subject_listed baseline_admitted
    _objectives_relevant objectives_discharged valid_roots valid_rules
    projection_respects all_outcomes_conservative
  constructor
  · intro a ha
    exact Qualification.soundness valid_roots valid_rules a (objectives_discharged a ha)
  · intro o ho
    have same := all_outcomes_conservative o ho
    have decisions : SameDecisions k catalogue project (Q B₀ R₀) (Q (B₁ o) (R₁ o)) :=
      same_decisions_of_projection_eq
        (projection_respects (Q B₀ R₀) (Q (B₁ o) (R₁ o)) same)
    exact ⟨same, decisions, (decisions.1 subject).symm.trans baseline_admitted⟩

#print axioms closure_included_of_roots_rules
#print axioms basis_conservative_iff
#print axioms full_closure_claim
#print axioms positive_extension_redundant_iff
#print axioms positive_additions_redundant_iff
#print axioms review_roots_redundant_iff
#print axioms review_rules_redundant_iff
#print axioms uniform_positive_additions_redundant_iff
#print axioms same_decisions_of_projection_eq
#print axioms relevant_claim
#print axioms same_decisions_of_full_closure
#print axioms omission_claim

end ReviewStatement
