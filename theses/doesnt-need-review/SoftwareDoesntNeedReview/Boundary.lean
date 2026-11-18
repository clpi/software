import SoftwareDoesntNeedReview.Reviewer
import SoftwareDoesntNeedReview.Chain
import SoftwareIsComposable.Admission

namespace SoftwareDoesntNeedReview

namespace Boundary

def unicodeBad : Release :=
  { cells := [
      { symbol := Sym.parse, axis := Ax.roundtrip, status := Status.ok },
      { symbol := Sym.parse, axis := Ax.unicode, status := Status.bad }] }

def unicodeOk : Release :=
  { cells := [
      { symbol := Sym.parse, axis := Ax.roundtrip, status := Status.ok },
      { symbol := Sym.parse, axis := Ax.unicode, status := Status.ok }] }

def bare : Certifier :=
  { watched := [(Sym.parse, Ax.roundtrip)], tests := [] }

def outside (s : Sym) (a : Ax) (R : Release) : Bool :=
  behaviorAt R s a == some Status.bad

def validWitness (w : Chain.Quantifiable.Witness) : Bool :=
  decide (w.events > 0)

def cellExec : Sym → Ax → Chain.Quantifiable.Execution
  | Sym.parse, Ax.roundtrip => ⟨0⟩
  | Sym.parse, Ax.unicode => ⟨1⟩
  | Sym.parse, Ax.bytes => ⟨2⟩
  | Sym.serialize, Ax.roundtrip => ⟨3⟩
  | Sym.serialize, Ax.unicode => ⟨4⟩
  | Sym.serialize, Ax.bytes => ⟨5⟩

def ledger (w : List (Sym × Ax)) (R : Release) : List Chain.Quantifiable.Witness :=
  w.filterMap fun (s, a) =>
    match behaviorAt R s a with
    | some _ => some ⟨(cellExec s a).id, 1⟩
    | none => none

def roster : List Chain.Quantifiable.Execution :=
  [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩]

theorem boundary_missed_by_certifier :
    firstRefusal bare.watched unicodeBad = CertVerdict.accept ∧
      outside Sym.parse Ax.unicode unicodeBad = true ∧
      Chain.Quantifiable.recorded validWitness (ledger bare.watched unicodeBad)
        (cellExec Sym.parse Ax.unicode) = false ∧
      cellExec Sym.parse Ax.unicode ∈
        Chain.Quantifiable.missing validWitness (ledger bare.watched unicodeBad) roster := by
  decide

theorem boundary_legacy_witness_insufficient :
    (∃ w, Chain.Quantifiable.Witnessed (cellExec Sym.parse Ax.unicode) w) ∧
      Chain.Quantifiable.recorded validWitness (ledger bare.watched unicodeBad)
        (cellExec Sym.parse Ax.unicode) = false := by
  refine ⟨Chain.Quantifiable.unrestricted_witness _, ?_⟩
  decide

theorem boundary_roster_not_mediated :
    ¬ (∀ e, e ∈ roster →
        Chain.Quantifiable.recorded validWitness (ledger bare.watched unicodeBad) e = true) := by
  intro h
  have hmem : cellExec Sym.parse Ax.unicode ∈ roster := by decide
  have hrec := h (cellExec Sym.parse Ax.unicode) hmem
  have hfalse :
      Chain.Quantifiable.recorded validWitness (ledger bare.watched unicodeBad)
        (cellExec Sym.parse Ax.unicode) = false := by decide
  rw [hfalse] at hrec
  cases hrec

theorem boundary_no_platform_premise :
    ¬ Nonempty (Chain.Quantifiable.PlatformPremise validWitness
        (ledger bare.watched unicodeBad) roster) := by
  intro ⟨P⟩
  exact boundary_roster_not_mediated
    (Chain.Quantifiable.coverage P)

theorem residual_unwatched_cell :
    factsOf bare unicodeOk = factsOf bare unicodeBad ∧
      outside Sym.parse Ax.unicode unicodeOk = false ∧
      outside Sym.parse Ax.unicode unicodeBad = true ∧
      watchedHas bare.watched Sym.parse Ax.unicode = false := by
  decide

def ThroughFacts (o : Release → Bool) (C : Certifier) : Prop :=
  ∀ R1 R2, factsOf C R1 = factsOf C R2 → o R1 = o R2

theorem outside_not_through_facts :
    ¬ ThroughFacts (outside Sym.parse Ax.unicode) bare := by
  intro h
  have hfacts : factsOf bare unicodeOk = factsOf bare unicodeBad := by decide
  have hbits := h unicodeOk unicodeBad hfacts
  have hleft : outside Sym.parse Ax.unicode unicodeOk = false := by decide
  have hright : outside Sym.parse Ax.unicode unicodeBad = true := by decide
  rw [hleft, hright] at hbits
  cases hbits

theorem bad_cell_not_qualified (old new : SoftwareIsComposable.SymbolProfile) (b : Nat)
    (hb : b ∈ old.behaviors) (hmiss : ¬ b ∈ new.behaviors) :
    SoftwareIsComposable.symbolAdmitted old new = false := by
  cases h : SoftwareIsComposable.symbolAdmitted old new with
  | false => rfl
  | true =>
    exact False.elim (hmiss ((SoftwareIsComposable.symbolAdmitted_iff.mp h).keeps b hb))

structure SpecRight where
  intended : List (Sym × Ax)
  watched : List (Sym × Ax)
  exact : ∀ s a, watchedHas intended s a = watchedHas watched s a

structure CellsObserved where
  intended : List (Sym × Ax)
  observed : ∀ (R : Release) (s : Sym) (a : Ax),
    watchedHas intended s a = true → behaviorAt R s a ≠ none

theorem redundant_under_premises (spec : SpecRight) (cov : CellsObserved)
    (R : Release) (s : Sym) (a : Ax)
    (hagree : cov.intended = spec.intended)
    (hint : watchedHas spec.intended s a = true)
    (hbad : behaviorAt R s a = some Status.bad) :
    refusesCell spec.watched R s a = true := by
  have hobs : behaviorAt R s a ≠ none := by
    have hmem : watchedHas cov.intended s a = true := by simpa [hagree] using hint
    exact cov.observed R s a hmem
  cases hbeh : behaviorAt R s a with
  | none => exact False.elim (hobs hbeh)
  | some st =>
    cases st with
    | ok => simp [hbad] at hbeh
    | bad =>
      have hw : watchedHas spec.watched s a = true := by simpa [spec.exact s a] using hint
      have hb : (behaviorAt R s a == some Status.bad) = true := by
        simp [hbeh]
        rfl
      exact refuses_of_mem spec.watched R s a hw hb

end Boundary

end SoftwareDoesntNeedReview
