import CanonicalDominance
import ComparisonContract
import FiniteFrontier
import SoftwareIsQuantifiable.Interface
import ThreeValuedGate

open SoftwareIsQuantifiable

namespace Red

inductive Job where
  | cheap
  | dear
  deriving DecidableEq, Repr

inductive Tone where
  | intended
  | stray
  | gap
  | unknown
  deriving DecidableEq, Repr

def meant (tone : Tone) : Bool :=
  match tone with
  | .intended => true
  | .stray => false
  | .gap => false
  | .unknown => false

theorem unknown : meant .unknown = false := rfl

def jobs : List Job := [.cheap, .dear]

def blind (job : Job) : List (Option Int) :=
  match job with
  | .cheap => [none]
  | .dear => [some 1]

def filled (job : Job) : List (Option Int) :=
  match job with
  | .cheap => [some (Int.ofNat 0)]
  | .dear => [some (Int.ofNat 1)]

def tone (job : Job) : Tone :=
  match job with
  | .cheap => .unknown
  | .dear => .intended

theorem toneunknown : tone .cheap = .unknown := rfl

theorem blocks (job : Job) :
    ¬ ThreeValuedGate.dominates ThreeValuedGate.contractMin (blind .cheap) (blind job) := by
  apply ThreeValuedGate.unknown_blocks_dominance (i := 0)
  · simp [ThreeValuedGate.contractMin]
  · cases job <;> decide

theorem canonical (job : Job) :
    ¬ Interface.dominates (ThreeValuedGate.measureSpace ThreeValuedGate.contractMin)
      (ThreeValuedGate.toProfile ThreeValuedGate.contractMin (blind .cheap))
      (ThreeValuedGate.toProfile ThreeValuedGate.contractMin (blind job)) := by
  apply ThreeValuedGate.unknown_blocks_dominance_canonical (i := 0)
  · simp [ThreeValuedGate.contractMin]
  · cases job <;> decide

theorem agrees :
    ThreeValuedGate.dominates ThreeValuedGate.contractMin (filled .cheap) (filled .dear) ↔
      Interface.dominates CanonicalDominance.oneSpace
        (CanonicalDominance.oneProfile 0) (CanonicalDominance.oneProfile 1) := by
  have hgate := ThreeValuedGate.known_agrees_canonical ThreeValuedGate.contractMin [0] [1]
    (by simp [ThreeValuedGate.contractMin]) (by simp [ThreeValuedGate.contractMin])
  have hcheap : filled .cheap = [0].map (fun n => some (Int.ofNat n)) := by decide
  have hdear : filled .dear = [1].map (fun n => some (Int.ofNat n)) := by decide
  rw [hcheap, hdear]
  have hread0 := ThreeValuedGate.toReadings_ofNat ThreeValuedGate.contractMin [0]
    (by simp [ThreeValuedGate.contractMin])
  have hread1 := ThreeValuedGate.toReadings_ofNat ThreeValuedGate.contractMin [1]
    (by simp [ThreeValuedGate.contractMin])
  have hspace : ThreeValuedGate.measureSpace ThreeValuedGate.contractMin =
      CanonicalDominance.oneSpace := by
    simp [ThreeValuedGate.measureSpace, ThreeValuedGate.directionPolarity, ThreeValuedGate.contractMin,
      CanonicalDominance.oneSpace]
  simp [ThreeValuedGate.toProfile, hread0, hread1, hspace, CanonicalDominance.oneProfile] at hgate
  exact hgate

theorem wins :
    ThreeValuedGate.dominates ThreeValuedGate.contractMin (filled .cheap) (filled .dear) := by
  rw [agrees]
  exact (CanonicalDominance.one_iff 0 1).mp (by decide)

def domblind (y x : Job) : Bool :=
  ThreeValuedGate.dominatesB ThreeValuedGate.contractMin (blind y) (blind x)

def domfilled (y x : Job) : Bool :=
  ThreeValuedGate.dominatesB ThreeValuedGate.contractMin (filled y) (filled x)

theorem shifts : FiniteFrontier.frontier jobs domblind ≠ FiniteFrontier.frontier jobs domfilled := by
  decide

theorem rejects :
    FiniteFrontier.certificate jobs [.dear] domfilled = false := by
  decide

theorem keeps :
    FiniteFrontier.certificate jobs [.cheap] domfilled = true := by
  decide

def filledspace : ThreeValuedGate.FiniteSpace Job ThreeValuedGate.contractMin where
  candidates := jobs
  readings := filled
  nothingOutside := by
    intro job
    cases job <;> decide
  noCoverageGaps := by
    intro job _ i hi
    have hi0 : i = 0 := by
      have hi1 : i < 1 := by simpa [ThreeValuedGate.contractMin] using hi
      omega
    subst hi0
    cases job <;> simp [filled, ThreeValuedGate.reading]

theorem guarded (job : Job) (h : job ∈ FiniteFrontier.frontier jobs domfilled) :
    ∀ other, ComparisonContract.dominates ThreeValuedGate.contractMin
      (ThreeValuedGate.materialized ThreeValuedGate.contractMin (filled other))
      (ThreeValuedGate.materialized ThreeValuedGate.contractMin (filled job)) = false :=
  ThreeValuedGate.frontier_no_dominator filledspace job h

end Red
