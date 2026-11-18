import SoftwareDoesntNeedReview.Boundary
import SoftwareDoesntNeedReview.Mechanize
import SoftwareDoesntNeedReview.Chain
import SoftwareIsComposable.Admission

namespace SoftwareDoesntNeedReview

namespace Controls

open Boundary

def unicodeTest : Test :=
  { symbol := Sym.parse
    axis := Ax.unicode
    reads := [(Sym.parse, Ax.unicode)]
    pred := predIsBad }

def unicodeCriterion (R : Release) : Bool :=
  testFires unicodeTest R

theorem control_before_misses :
    firstRefusal bare.watched unicodeBad = CertVerdict.accept := by
  decide

theorem control_predicate_catches :
    unicodeCriterion unicodeBad = true := by
  decide

theorem control_after_refuses_by_name :
    namesRefusal (install bare unicodeTest).tests unicodeBad Sym.parse Ax.unicode = true := by
  decide

theorem control_predicate_is_finite_table :
    ∃ row, row ∈ table predIsBad 1 ∧ row.1 = [Status.bad] ∧ row.2 = true :=
  mechanized_value_is_table_row predIsBad 1 [Status.bad] rfl rfl

def baseBytes : Release :=
  { cells := [{ symbol := Sym.serialize, axis := Ax.bytes, status := Status.ok }] }

def candBytes : Release :=
  { cells := [{ symbol := Sym.serialize, axis := Ax.bytes, status := Status.bad }] }

def byteWatch : List (Sym × Ax) := [(Sym.serialize, Ax.bytes)]

def byteCert : Certifier :=
  { watched := byteWatch, tests := [] }

theorem control_human_approves :
    alwaysApprove (sightOf byteCert baseBytes candBytes) = true := rfl

theorem control_human_regression_refused :
    Chain.Regress.verdict byteWatch baseBytes candBytes =
      CertVerdict.refuse Sym.serialize Ax.bytes := by
  decide

def bytesOld : SoftwareIsComposable.SymbolProfile :=
  { id := 1, behaviors := [2], costs := [{ lo := 0, hi := 0 }] }

def bytesNew : SoftwareIsComposable.SymbolProfile :=
  { id := 1, behaviors := [], costs := [{ lo := 0, hi := 0 }] }

theorem control_human_regression_equiv :
    (Chain.Regress.verdict byteWatch baseBytes candBytes =
        CertVerdict.refuse Sym.serialize Ax.bytes) ↔
      (SoftwareIsComposable.symbolVerdict bytesOld bytesNew =
        SoftwareIsComposable.Verdict.refused
          (SoftwareIsComposable.Reason.behaviorDropped 1 2)) := by
  decide

def intendedParse : List (Sym × Ax) :=
  [(Sym.parse, Ax.roundtrip), (Sym.parse, Ax.unicode)]

def needsSpecReview (intended watched : List (Sym × Ax)) : Bool :=
  intended.any fun (s, a) => watchedHas watched s a == false

theorem control_incomplete_passes :
    firstRefusal bare.watched unicodeBad = CertVerdict.accept ∧
      needsSpecReview intendedParse bare.watched = true := by
  decide

theorem safety_refused_by_name :
    Chain.Safe.verdict [(Sym.parse, Ax.roundtrip)]
      { cells := [{ symbol := Sym.parse, axis := Ax.roundtrip, status := Status.bad }] } =
      CertVerdict.refuse Sym.parse Ax.roundtrip := by
  decide

def safeOld : SoftwareIsComposable.SymbolProfile :=
  { id := 0, behaviors := [0], costs := [{ lo := 0, hi := 0 }] }

def safeNew : SoftwareIsComposable.SymbolProfile :=
  { id := 0, behaviors := [], costs := [{ lo := 0, hi := 0 }] }

theorem safety_equiv :
    (Chain.Safe.verdict [(Sym.parse, Ax.roundtrip)]
        { cells := [{ symbol := Sym.parse, axis := Ax.roundtrip, status := Status.bad }] } =
      CertVerdict.refuse Sym.parse Ax.roundtrip) ↔
      (SoftwareIsComposable.symbolVerdict safeOld safeNew =
        SoftwareIsComposable.Verdict.refused
          (SoftwareIsComposable.Reason.behaviorDropped 0 0)) := by
  decide

end Controls

end SoftwareDoesntNeedReview
