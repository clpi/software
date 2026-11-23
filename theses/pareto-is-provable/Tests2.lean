import Second
import Tests

/- Executable agreement and control tests for lane 2, run by
   the kernel at the closing pin. Every test is a decidable
   equality or a decidable proposition over the lane 1 test
   instance (three candidates, two axes) extended by one
   joined candidate; a failing test is a failing build. The
   first-instance evidence (18 candidates, 7 axes) is lanes 3
   to 5's executed work, cited in the home record: lane 4's
   controls for obligations 15 and 16 and its 24 per-operation
   equality receipts for obligation 17, and lane 5's checker
   comparison for obligation 12. -/

namespace checks

def four : cand := ⟨4, some 40⟩

def rfour : row := ⟨four, [3, 1]⟩

/-- Obligation 12, executed instance: the checker frontier
    equals the solver frontier on the instance, and both are
    the first two rows. -/
theorem checker : twelve.front tests.axes tests.rows =
    core.front tests.axes tests.rows ∧
    core.front tests.axes tests.rows = [tests.rone, tests.rtwo] := by
  decide

/-- Obligation 15, executed instance: the third candidate
    touches the first row's frontier verdict (its cone holds
    the pair from the third row), and an absent candidate
    touches nothing and leaves the frontier exactly as it was
    under a swap naming it. -/
theorem touch : fifteen.touches tests.third tests.rows tests.rone ∧
    ¬ fifteen.touches ⟨9, some 90⟩ tests.rows tests.rone ∧
    core.front tests.axes
      (fourteen.swap tests.rows ⟨9, some 90⟩ ⟨⟨9, some 90⟩, [0, 0]⟩) =
    core.front tests.axes tests.rows := by
  refine ⟨?_, ?_, by decide⟩
  · exact (fifteen.scope tests.rows tests.rone (by decide)
      tests.third).mpr (Or.inl ⟨tests.rthree, by decide, rfl⟩)
  · intro h
    rw [fifteen.scope tests.rows tests.rone (by decide)] at h
    cases h with
    | inl h =>
      obtain ⟨o, ho, hwho⟩ := h
      have hdec : ¬ (∃ o ∈ tests.rows, o.who = ⟨9, some 90⟩) := by
        decide
      exact hdec ⟨o, ho, hwho⟩
    | inr h => cases h

/-- Obligation 16, executed controls: an unchanged cone's
    certificate holds; a cone with exactly one changed cell
    (the first cell's value changed) refuses. -/
theorem carry : sixteen.holds
      [tests.cellone, tests.cellthree] [tests.cellone, tests.cellthree] = true ∧
    sixteen.holds [tests.cellone, tests.cellthree]
      [tests.cellone, ⟨1, 1, 9999, some tests.bone, 1⟩] = false := by
  decide

/-- Obligation 17, executed instance: over the operation
    sequence join-then-withdraw, the incrementally maintained
    frontier and state equal the from-scratch ones, as lists
    on this instance (the general proof is set equality). -/
theorem walk : (seventeen.track tests.axes tests.rows
      (core.front tests.axes tests.rows)
      [.join rfour, .drop tests.second]).1 =
    seventeen.walk tests.rows [.join rfour, .drop tests.second] ∧
    (seventeen.track tests.axes tests.rows
      (core.front tests.axes tests.rows)
      [.join rfour, .drop tests.second]).2 =
    core.front tests.axes
      (seventeen.walk tests.rows [.join rfour, .drop tests.second]) := by
  decide

def base : eighteen.tuple := ⟨9, 1, 1, 1⟩

def good : eighteen.record := ⟨base, true⟩

/-- Obligation 18, executed control: the verdict under the
    tuple in force is accepted; the same verdict re-presented
    with exactly one tuple component changed — each of the
    four components in turn — is not accepted. -/
theorem tuple : eighteen.accept base good = true ∧
    eighteen.accept ⟨10, 1, 1, 1⟩ good = false ∧
    eighteen.accept ⟨9, 2, 1, 1⟩ good = false ∧
    eighteen.accept ⟨9, 1, 2, 1⟩ good = false ∧
    eighteen.accept ⟨9, 1, 1, 2⟩ good = false := by
  decide

/-- Obligation 20, executed control: one cell change (cell 1)
    on a copy of the instance's verdict table reopens exactly
    the records whose cones contain that cell, and keeps
    exactly the rest. -/
theorem reopen : twenty.reopen 1 [tests.vone, tests.vtwo, tests.vthree] =
    [tests.vone, tests.vthree] ∧
    twenty.kept 1 [tests.vone, tests.vtwo, tests.vthree] =
    [tests.vtwo] := by
  decide

end checks
