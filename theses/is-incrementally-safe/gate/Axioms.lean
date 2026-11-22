import Lean
import SoftwareIsIncrementallySafe
import Family
import DependencyModules
import RenameReorderAxioms
import FamilyAxioms
import OrderedIncrementAxioms
import SubmittedTraceSys
import NatReprInjective

/-!
Gate: walk every named declaration in this repository's modules.

Compiler and elaborator internals (names with a `_` component, such as
`_spec_1`, `_proof_1`, `match_1`) are not checked one by one: their axioms are
counted through every declaration that uses them.

Fails when any declaration is an axiom, is unsafe, is opaque (which is how `partial`
and `implemented_by` surface), or depends on an axiom other than `propext`,
`Quot.sound` and `Classical.choice`. `sorry` surfaces as `sorryAx`,
`native_decide` as `Lean.ofReduceBool`; both fail here.
-/

open Lean Elab Command

def gateOwnRoots : List Lean.Name :=
  [`SoftwareIsIncrementallySafe, `Family, `DependencyModules, `RenameReorderAxioms,
   `FamilyAxioms, `OrderedIncrementAxioms, `SubmittedTraceSys, `NatReprInjective]

def gateAllowed : List Lean.Name := [``propext, ``Quot.sound, ``Classical.choice]

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut ownMods : Array Lean.Name := #[]
  for m in mods do
    if gateOwnRoots.contains m.getRoot then ownMods := ownMods.push m
  let mut decls := 0
  let mut theorems := 0
  let mut skipped := 0
  let mut bad : Array String := #[]
  let mut hist : Std.HashMap Lean.Name Nat := {}
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless gateOwnRoots.contains m.getRoot do continue
    let user := (privateToUserName? n).getD n
    if user.isInternal then
      skipped := skipped + 1
      continue
    decls := decls + 1
    if ci matches .thmInfo _ then theorems := theorems + 1
    if ci matches .axiomInfo _ then bad := bad.push s!"axiom declared: {n} in {m}"
    if ci.isUnsafe then bad := bad.push s!"unsafe: {n} in {m}"
    if ci matches .opaqueInfo _ then bad := bad.push s!"opaque: {n} in {m}"
    let axs ← collectAxioms n
    for a in axs do
      hist := hist.insert a (hist.getD a 0 + 1)
      unless gateAllowed.contains a do bad := bad.push s!"axiom {a} used by {n} in {m}"
  logInfo m!"gate: {ownMods.size} modules, {decls} declarations, {theorems} theorems, {skipped} internal names reached only through them"
  for (a, k) in hist.toList do
    logInfo m!"gate: {a} used by {k} declarations"
  if decls == 0 then throwError "gate: no declarations found; module roots are wrong"
  unless bad.isEmpty do
    throwError m!"gate: {bad.size} violations:\n{String.intercalate "\n" bad.toList}"
