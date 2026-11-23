import Qualification
import Admission
import AdmissionHypergraph
import ScopedEvidence
import ScopedFrontier
import ExecutableClosure
import SoftwareIsQuantifiable.Interface
import SoftwareIsQuantifiable.Coverage

namespace ReviewStatement

abbrev Q {A : Type} (B : A → Prop) (R : List A → A → Prop) :=
  Qualification.Derives B R

def BasisConservative {A : Type}
    (B₀ B₁ : A → Prop) (R₀ R₁ : List A → A → Prop) : Prop :=
  (∀ a, B₁ a → Q B₀ R₀ a) ∧ Qualification.Closed R₁ (Q B₀ R₀) ∧
  (∀ a, B₀ a → Q B₁ R₁ a) ∧ Qualification.Closed R₀ (Q B₁ R₁)

def SameDecisions {A : Type}
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (Q₀ Q₁ : A → Prop) : Prop :=
  (∀ s, ScopedFrontier.admitted k s (project Q₀ s) =
    ScopedFrontier.admitted k s (project Q₁ s)) ∧
  ScopedFrontier.select k catalogue (project Q₀) =
    ScopedFrontier.select k catalogue (project Q₁)

def FullClosureClaim : Prop :=
  ∀ (A : Type) (B₀ B₁ : A → Prop) (R₀ R₁ : List A → A → Prop),
    BasisConservative B₀ B₁ R₀ R₁ ↔
      ∀ a, Q B₀ R₀ a ↔ Q B₁ R₁ a

def SameRelevant {A : Type} (relevant Q₀ Q₁ : A → Prop) : Prop :=
  ∀ a, relevant a → (Q₀ a ↔ Q₁ a)

def RespectsRelevant {A : Type} (relevant : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input) : Prop :=
  ∀ X Y : A → Prop, SameRelevant relevant X Y → project X = project Y

def RelevantClaim : Prop :=
  ∀ (A : Type) (B₀ B₁ : A → Prop) (R₀ R₁ : List A → A → Prop)
    (relevant : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject),
    RespectsRelevant relevant project →
    SameRelevant relevant (Q B₀ R₀) (Q B₁ R₁) →
    SameDecisions k catalogue project (Q B₀ R₀) (Q B₁ R₁)

def OmissionClaim : Prop :=
  ∀ (A Outcome : Type)
    (B₀ : A → Prop) (R₀ : List A → A → Prop)
    (B₁ : Outcome → A → Prop) (R₁ : Outcome → List A → A → Prop)
    (allowed : Outcome → Prop) (relevant required TrueAt : A → Prop)
    (project : (A → Prop) → ScopedFrontier.Subject → ScopedFrontier.Input)
    (k : ScopedFrontier.Contract) (catalogue : List ScopedFrontier.Subject)
    (subject : ScopedFrontier.Subject),
    (∃ a, required a) →
    (∃ o, allowed o) →
    subject ∈ catalogue →
    ScopedFrontier.admitted k subject (project (Q B₀ R₀) subject) = true →
    (∀ a, required a → relevant a) →
    (∀ a, required a → Q B₀ R₀ a) →
    (∀ a, B₀ a → TrueAt a) →
    Qualification.Closed R₀ TrueAt →
    RespectsRelevant relevant project →
    (∀ o, allowed o → SameRelevant relevant (Q B₀ R₀) (Q (B₁ o) (R₁ o))) →
    (∀ a, required a → TrueAt a) ∧
    (∀ o, allowed o →
      SameRelevant relevant (Q B₀ R₀) (Q (B₁ o) (R₁ o)) ∧
      SameDecisions k catalogue project (Q B₀ R₀) (Q (B₁ o) (R₁ o)) ∧
      ScopedFrontier.admitted k subject (project (Q (B₁ o) (R₁ o)) subject) = true)

#check FullClosureClaim
#check RelevantClaim
#check OmissionClaim
#check Qualification.soundness
#check ExecutableClosure.checkedClose_admitted
#check AdmissionHypergraph.graph
#check ScopedFrontier.admitted_exact
#check ScopedFrontier.selected_exact
#check SoftwareIsQuantifiable.Coverage.scoped_audit_complete
#check SoftwareIsQuantifiable.Interface.noWorse

end ReviewStatement
