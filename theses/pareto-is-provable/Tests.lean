import Pareto

/- Executable agreement and control tests for lane 1, run by the
   kernel at the closing pin. Every test is a decidable equality
   over a concrete instance; a failing test is a failing build.
   The instance holds three candidates on two axes: the first
   two rows are equal on all axes, the third differs from the
   first on exactly one axis. -/

namespace tests

def aone : axis := ⟨1, some true, some 5, some 7, 1, 0⟩

def atwo : axis := ⟨2, some false, some 5, some 8, 1, 0⟩

def first : cand := ⟨1, some 10⟩

def second : cand := ⟨2, some 20⟩

def third : cand := ⟨3, some 30⟩

def dupe : cand := ⟨1, some 99⟩

def rone : row := ⟨first, [5, 1]⟩

def rtwo : row := ⟨second, [5, 1]⟩

def rthree : row := ⟨third, [4, 1]⟩

def axes : List axis := [aone, atwo]

def rows : List row := [rone, rtwo, rthree]

def pairs : List (row × row) :=
  [(rone, rone), (rone, rtwo), (rone, rthree),
   (rtwo, rone), (rtwo, rtwo), (rtwo, rthree),
   (rthree, rone), (rthree, rtwo), (rthree, rthree)]

def sp : space := ⟨[first, second, third], axes⟩

def tb : table := ⟨rows, 9⟩

/-- Obligation 9 differential test: solver and checker agree on
    the full pair set of the instance, all nine ordered pairs. -/
theorem agree : ∀ p ∈ pairs, verdict axes p.1 p.2 = cross axes p.1 p.2 := by
  decide

/-- Obligation 9 control: rows equal on all axes dominate
    neither way. -/
theorem equal : verdict axes rone rtwo = false ∧ verdict axes rtwo rone = false := by
  decide

/-- Obligation 9 control: a pair differing on exactly one axis
    dominates one way only. -/
theorem single : verdict axes rone rthree = true ∧ verdict axes rthree rone = false := by
  decide

/-- Obligation 9 control: no candidate dominates itself. -/
theorem self : verdict axes rone rone = false := by
  decide

/-- Obligation 1 checker pass on the instance, and its refusal
    on a table missing one declared row. -/
theorem space : one.tally sp tb = true ∧ one.tally sp ⟨[rone, rtwo], 9⟩ = false := by
  decide

def pres : List cand := [first, second, third, dupe]

def log : List two.entry :=
  [⟨first, two.disp.entered, none⟩, ⟨second, two.disp.entered, none⟩,
   ⟨third, two.disp.entered, none⟩,
   ⟨dupe, two.disp.refused two.reason.dupe, some first⟩]

/-- Obligation 2 checker pass: the log accounts for every
    presentation, the duplicate refusal naming its entry. -/
theorem logtest : two.accounted pres log = true := by
  decide

/-- Obligation 4 instance: withdrawal then entry, exactly. -/
theorem step : four.evolve [first, second] [third] [second] = [first, third] := by
  decide

/-- Obligation 5 checker passes on the instance: every axis
    fully declared, every declaration before its values. -/
theorem declared : sp.axes.all five.fullb = true := by
  decide

def bone : receipt := ⟨1, 1, 7, 1, 9, 7001⟩

def btwo : receipt := ⟨1, 2, 8, 1, 9, 8001⟩

def bthree : receipt := ⟨2, 1, 7, 1, 9, 7002⟩

def receipts : List receipt := [bone, btwo, bthree]

/-- Obligation 6 agreement test: re-running the named instrument
    at the named version on the named candidate reproduces every
    cell value of the instance, cell by cell. -/
theorem bind : receipts.map (fun r => run r.tool r.who) = receipts.map receipt.val := by
  decide

def cellone : cell := ⟨1, 1, 7001, some bone, 1⟩

def celltwo : cell := ⟨1, 2, 8001, none, 1⟩

def cellthree : cell := ⟨2, 1, 7002, some bthree, 1⟩

theorem timing : five.earlier sp [cellone, celltwo, cellthree] = true := by
  decide

/-- Obligation 7 control: the table with exactly one receipt
    removed (the second cell) yields UNMEASURED naming that
    cell, and the fully receipted cone accepts. -/
theorem gap : seven.assess [cellone, celltwo, cellthree] = outcome.unmeasured celltwo ∧
    seven.assess [cellone, cellthree] = outcome.accept := by
  decide

def vone : eight.verdictrec := ⟨1, [1]⟩

def vtwo : eight.verdictrec := ⟨2, [2]⟩

def vthree : eight.verdictrec := ⟨3, [1, 2]⟩

/-- Obligation 8 control: reversing the first axis direction on
    a copy of the table invalidates exactly the verdicts whose
    cones contain that axis, and the pair verdict flips. -/
theorem touch : eight.touched aone [vone, vtwo, vthree] = [vone, vthree] ∧
    verdict [eight.bump aone false, atwo] rthree rone = true ∧
    (eight.bump aone false).ver = aone.ver + 1 := by
  decide

end tests
