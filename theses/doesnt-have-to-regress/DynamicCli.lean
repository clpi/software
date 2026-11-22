import GateExe.Parser
import Dynamic.Engine
import Dynamic.History

set_option autoImplicit false

namespace DynamicCli

open SoftwareDoesntRegress
open SoftwareDoesntRegress.Dynamic

structure ContractCell where
  key : Nat
  required : List Nat
  allowed : List Nat
  deriving DecidableEq, Repr

structure ContractData where
  context : Nat
  keys : List Nat
  cells : List ContractCell
  deriving DecidableEq, Repr

structure ReleaseCell where
  key : Nat
  offered : List Nat
  possible : List Nat
  cost : Nat × Nat
  deriving DecidableEq, Repr

structure ReleaseData where
  id : Nat
  context : Nat
  cells : List ReleaseCell
  deriving DecidableEq, Repr

def ContractData.cell (q : ContractData) (key : Nat) : ContractCell :=
  (q.cells.find? fun cell => cell.key == key).getD ⟨key, [], []⟩

def ContractData.toContract (q : ContractData) : Audit.Contract Nat Nat Nat Nat :=
  { context := q.context, keys := q.keys,
    prior := fun key => ⟨(q.cell key).required⟩,
    allowed := fun key => (q.cell key).allowed }

def ReleaseData.cell (r : ReleaseData) (key : Nat) : ReleaseCell :=
  (r.cells.find? fun cell => cell.key == key).getD ⟨key, [], [], (0, 0)⟩

def ReleaseData.toRelease (r : ReleaseData) : Audit.ScopedRelease Nat Nat Nat Nat :=
  { context := r.context, profile := fun key =>
    { offered := ⟨(r.cell key).offered⟩,
      possible := (r.cell key).possible, cost := (r.cell key).cost } }

def ReleaseData.toArtifact (r : ReleaseData) : Engine.Artifact Nat Nat Nat Nat :=
  ⟨r.id, r.toRelease⟩

inductive Command where
  | query (candidate : ReleaseData)
  | arrive (event : Nat) (releases : List ReleaseData)
  | reconsider (event : Nat)
  | rollback (event release : Nat)
  | undo (event source : Nat)
  | strengthen (event : Nat) (contract : ContractData) (candidate : Option ReleaseData)
  | context (event context initial : Nat) (releases : List ReleaseData)
  deriving DecidableEq, Repr

def Command.identifier : Command → Option Nat
  | .query _ => none
  | .arrive id _ | .reconsider id | .rollback id _ | .undo id _ |
    .strengthen id _ _ | .context id _ _ _ => some id

def Command.name : Command → String
  | .query _ => "query"
  | .arrive _ _ => "arrive"
  | .reconsider _ => "reconsider"
  | .rollback _ _ => "rollback"
  | .undo _ _ => "undo"
  | .strengthen _ _ _ => "strengthen"
  | .context _ _ _ _ => "context"

structure Scenario where
  contract : ContractData
  initial : ReleaseData
  commands : List Command

def natOf : GateExe.J → Option Nat
  | .num n => some n
  | _ => none

def listOf {α : Type} (parse : GateExe.J → Option α) : GateExe.J → Option (List α)
  | .arr xs => xs.mapM parse
  | _ => none

def fieldsOnly (fields : List (String × GateExe.J)) (names : List String) : Bool :=
  fields.all fun field => names.contains field.1

def contractCellOf : GateExe.J → Option ContractCell
  | .obj fs => do
      if !fieldsOnly fs ["key", "required", "allowed"] then none else
      let key ← GateExe.lookup "key" fs >>= natOf
      let required ← GateExe.lookup "required" fs >>= GateExe.natList
      let allowed ← GateExe.lookup "allowed" fs >>= GateExe.natList
      pure ⟨key, required, allowed⟩
  | _ => none

def contractOf : GateExe.J → Option ContractData
  | .obj fs => do
      if !fieldsOnly fs ["context", "keys", "cells"] then none else
      let context ← GateExe.lookup "context" fs >>= natOf
      let keys ← GateExe.lookup "keys" fs >>= GateExe.natList
      let cells ← GateExe.lookup "cells" fs >>= listOf contractCellOf
      pure ⟨context, keys, cells⟩
  | _ => none

def pointOf : GateExe.J → Option (Nat × Nat)
  | .arr [.num a, .num b] => some (a, b)
  | _ => none

def releaseCellOf : GateExe.J → Option ReleaseCell
  | .obj fs => do
      if !fieldsOnly fs ["key", "offered", "possible", "cost"] then none else
      let key ← GateExe.lookup "key" fs >>= natOf
      let offered ← GateExe.lookup "offered" fs >>= GateExe.natList
      let possible ← GateExe.lookup "possible" fs >>= GateExe.natList
      let cost ← GateExe.lookup "cost" fs >>= pointOf
      pure ⟨key, offered, possible, cost⟩
  | _ => none

def releaseOf : GateExe.J → Option ReleaseData
  | .obj fs => do
      if !fieldsOnly fs ["id", "context", "cells"] then none else
      let id ← GateExe.lookup "id" fs >>= natOf
      let context ← GateExe.lookup "context" fs >>= natOf
      let cells ← GateExe.lookup "cells" fs >>= listOf releaseCellOf
      pure ⟨id, context, cells⟩
  | _ => none

def commandOf : GateExe.J → Option Command
  | .obj fs => do
      let op ← GateExe.lookup "op" fs
      match op with
      | .str "query" =>
          if !fieldsOnly fs ["op", "candidate"] then none else
          return .query (← GateExe.lookup "candidate" fs >>= releaseOf)
      | .str "arrive" =>
          if !fieldsOnly fs ["op", "event", "releases"] then none else
          return .arrive (← GateExe.lookup "event" fs >>= natOf)
            (← GateExe.lookup "releases" fs >>= listOf releaseOf)
      | .str "reconsider" =>
          if !fieldsOnly fs ["op", "event"] then none else
          return .reconsider (← GateExe.lookup "event" fs >>= natOf)
      | .str "rollback" =>
          if !fieldsOnly fs ["op", "event", "release"] then none else
          return .rollback (← GateExe.lookup "event" fs >>= natOf)
            (← GateExe.lookup "release" fs >>= natOf)
      | .str "undo" =>
          if !fieldsOnly fs ["op", "event", "source"] then none else
          return .undo (← GateExe.lookup "event" fs >>= natOf)
            (← GateExe.lookup "source" fs >>= natOf)
      | .str "strengthen" =>
          if !fieldsOnly fs ["op", "event", "contract", "candidate"] then none else
          let candidate ← match GateExe.lookup "candidate" fs with
            | none => some none
            | some value => some <$> releaseOf value
          return .strengthen (← GateExe.lookup "event" fs >>= natOf)
            (← GateExe.lookup "contract" fs >>= contractOf) candidate
      | .str "context" =>
          if !fieldsOnly fs ["op", "event", "context", "initial", "releases"] then none else
          return .context (← GateExe.lookup "event" fs >>= natOf)
            (← GateExe.lookup "context" fs >>= natOf)
            (← GateExe.lookup "initial" fs >>= natOf)
            (← GateExe.lookup "releases" fs >>= listOf releaseOf)
      | _ => none
  | _ => none

def parse (text : String) : Option Scenario := do
  let chars := text.toList
  let (value, rest) ← GateExe.parseValue (chars.length * 3 + 1) chars
  if GateExe.ws rest ≠ [] then none else
  match value with
  | .obj fs =>
      if !fieldsOnly fs ["contract", "initial", "commands"] then none else
      return ⟨← GateExe.lookup "contract" fs >>= contractOf,
        ← GateExe.lookup "initial" fs >>= releaseOf,
        ← GateExe.lookup "commands" fs >>= listOf commandOf⟩
  | _ => none

def validateContract (q : ContractData) : Except String Unit := do
  if q.keys.isEmpty then throw "contract has no protected keys"
  if !(decide q.keys.Nodup) then throw "duplicate protected key"
  if !(decide (q.cells.map ContractCell.key).Nodup) then throw "duplicate contract cell"
  if !(q.keys.all fun key => (q.cells.map ContractCell.key).contains key) then
    throw "contract is missing a protected-key cell"
  if !(q.cells.all fun cell => q.keys.contains cell.key) then
    throw "contract contains an undeclared-key cell"

def validateRelease (q : ContractData) (r : ReleaseData) : Except String Unit := do
  if !(decide (r.cells.map ReleaseCell.key).Nodup) then throw "duplicate release cell"
  if !(q.keys.all fun key => (r.cells.map ReleaseCell.key).contains key) then
    throw "release is missing a protected-key cell"

def findRelease (id : Nat) (releases : List ReleaseData) : Option ReleaseData :=
  releases.find? fun release => release.id == id

def validateBindings (archive news : List ReleaseData) : Except String Unit := do
  if !(decide (news.map ReleaseData.id).Nodup) then throw "duplicate release identifier"
  for release in news do
    match findRelease release.id archive with
    | none => pure ()
    | some prior =>
        if prior ≠ release then throw "release identifier is already bound to different data"

def archiveNew (archive news : List ReleaseData) : List ReleaseData :=
  archive ++ news.filter fun release => (findRelease release.id archive).isNone

structure Report where
  op : String
  status : String
  accepted : Bool
  evaluated : Nat
  reused : Nat

structure Receipt where
  command : Command
  report : Report

structure Runtime where
  contract : ContractData
  incumbent : ReleaseData
  archive : List ReleaseData
  observations : List ReleaseData
  cache : Incremental.Cache Nat Nat Nat Nat
  journal : History.Journal Nat Nat
  receipts : List Receipt
  totalEvaluated : Nat
  totalReused : Nat

def selectedData (id : Nat) (archive : List ReleaseData) : Except String ReleaseData :=
  match findRelease id archive with
  | some release => pure release
  | none => throw "engine selected an unarchived release identifier"

def startScenario (scenario : Scenario) : Except String (Runtime × Report) := do
  validateContract scenario.contract
  validateRelease scenario.contract scenario.initial
  let first := Incremental.recertify [] scenario.contract.toContract
    scenario.initial.toRelease scenario.initial.toRelease
  if !first.verdict then throw "initial release is not certified; no scenario started"
  let journal : History.Journal Nat Nat :=
    { current := fun key => if key = 0 then scenario.initial.id else
        if key = 1 then scenario.contract.context else 0,
      events := [] }
  let state : Runtime :=
    { contract := scenario.contract, incumbent := scenario.initial,
      archive := [scenario.initial], observations := [scenario.initial], cache := first.cache,
      journal := journal, receipts := [],
      totalEvaluated := first.evaluated, totalReused := first.reused }
  pure (state, ⟨"initialize", "certified", true, first.evaluated, first.reused⟩)

def runFresh (state : Runtime) (command : Command) : Except String (Runtime × Report) := do
  let q := state.contract.toContract
  let old := state.incumbent.toArtifact
  match command with
  | .query candidate =>
      validateRelease state.contract candidate
      validateBindings state.archive [candidate]
      let result := Incremental.recertify state.cache q old.release candidate.toRelease
      pure ({ state with cache := result.cache },
        ⟨"query", if result.verdict then "permitted" else "refused",
          result.verdict, result.evaluated, result.reused⟩)
  | .arrive _ releases =>
      for release in releases do validateRelease state.contract release
      validateBindings state.archive releases
      let archive := archiveNew state.archive releases
      let some result := Engine.select q state.cache old (releases.map ReleaseData.toArtifact) |
        throw "incumbent is invalid; arrival cannot publish a result"
      let incumbent ← selectedData result.incumbent.id archive
      let changed := incumbent.id != state.incumbent.id
      pure ({ state with
        incumbent := incumbent, archive := archive,
        observations := state.observations ++ releases, cache := result.cache },
        ⟨"arrive", if changed then "selected" else "unchanged", changed,
          result.evaluated, result.reused⟩)
  | .reconsider _ =>
      for release in state.archive do validateRelease state.contract release
      let some result := Engine.select q state.cache old
          (state.archive.map ReleaseData.toArtifact) |
        throw "incumbent is invalid; reconsideration cannot publish a result"
      let incumbent ← selectedData result.incumbent.id state.archive
      let changed := incumbent.id != state.incumbent.id
      pure ({ state with incumbent := incumbent, cache := result.cache },
        ⟨"reconsider", if changed then "selected" else "unchanged", changed,
          result.evaluated, result.reused⟩)
  | .rollback _ identifier =>
      let candidate ← match findRelease identifier state.archive with
        | some candidate => pure candidate
        | none => throw "rollback release is not in the current archive"
      validateRelease state.contract candidate
      let some result := Engine.deploy q state.cache old candidate.toArtifact |
        throw "incumbent is invalid; rollback cannot publish a result"
      let incumbent ← selectedData result.incumbent.id state.archive
      pure ({ state with incumbent := incumbent, cache := result.cache },
        ⟨"rollback", if result.accepted then "accepted" else "refused", result.accepted,
          result.evaluated, result.reused⟩)
  | .undo _ source =>
      let some recorded := History.lookup source state.journal.events |
        throw "undo source event is not recorded"
      let some inverseState := History.applyPatch state.journal.current (History.inverse recorded.patch) |
        throw "undo after-values no longer match the current state"
      if inverseState 1 ≠ state.contract.context then
        throw "undo cannot reverse a context epoch or its obligations"
      let candidate ← selectedData (inverseState 0) state.archive
      validateRelease state.contract candidate
      let some result := Engine.deploy q state.cache old candidate.toArtifact |
        throw "incumbent is invalid; undo cannot publish a result"
      let incumbent ← selectedData result.incumbent.id state.archive
      pure ({ state with incumbent := incumbent, cache := result.cache },
        ⟨"undo", if result.accepted then "accepted" else "refused", result.accepted,
          result.evaluated, result.reused⟩)
  | .strengthen _ nextContract proposed =>
      validateContract nextContract
      let candidate := proposed.getD state.incumbent
      validateRelease state.contract candidate
      validateRelease nextContract candidate
      validateBindings state.archive [candidate]
      let archive := archiveNew state.archive [candidate]
      for release in archive do
        if !(nextContract.keys.all fun key => (release.cells.map ReleaseCell.key).contains key) then
          throw "new scope needs reobservation: an archived release lacks a protected-key cell"
      let result := Engine.adopt q nextContract.toContract state.cache old candidate.toArtifact
      if result.accepted then
        let some selected := Engine.select nextContract.toContract result.cache result.incumbent
            (archive.map ReleaseData.toArtifact) |
          throw "adopted release failed recertification; no state was committed"
        let incumbent ← selectedData selected.incumbent.id archive
        pure ({ state with
          contract := nextContract, incumbent := incumbent, archive := archive,
          observations := state.observations ++ [candidate], cache := selected.cache },
          ⟨"strengthen", "adopted", true,
            result.evaluated + selected.evaluated, result.reused + selected.reused⟩)
      else
        let some selected := Engine.select q result.cache old (archive.map ReleaseData.toArtifact) |
          throw "incumbent is invalid after refused contract; no state was committed"
        let incumbent ← selectedData selected.incumbent.id archive
        let changed := incumbent.id != state.incumbent.id
        pure ({ state with
          incumbent := incumbent, archive := archive,
          observations := state.observations ++ [candidate], cache := selected.cache },
          ⟨"strengthen", if changed then "refused-selected" else "refused", false,
            result.evaluated + selected.evaluated, result.reused + selected.reused⟩)
  | .context _ context initial releases =>
      if context = state.contract.context then throw "context event must establish a new context"
      if initial ≠ state.incumbent.id then
        throw "context event cannot switch artifact while establishing its baseline"
      if !(decide (releases.map ReleaseData.id).Nodup) then
        throw "duplicate reobserved release identifier"
      if !(state.archive.all fun prior => (releases.map ReleaseData.id).contains prior.id) then
        throw "context event omits an archived artifact"
      if !(releases.all fun release => (state.archive.map ReleaseData.id).contains release.id) then
        throw "context event introduces an unarchived artifact"
      let nextContract := { state.contract with context := context }
      for release in releases do
        validateRelease nextContract release
        if release.context ≠ context then throw "reobservation has the wrong context"
      let baseline ← selectedData initial releases
      let some result := Engine.select nextContract.toContract state.cache baseline.toArtifact
          (releases.map ReleaseData.toArtifact) |
        throw "new-context incumbent is not certified; epoch was not published"
      let incumbent ← selectedData result.incumbent.id releases
      pure ({ state with
        contract := nextContract, incumbent := incumbent, archive := releases,
        observations := state.observations ++ releases, cache := result.cache },
        ⟨"context", "reobserved", true, result.evaluated, result.reused⟩)

/-- The journal records selector/context values; cumulative contracts,
    cached evidence, observations, and command receipts only move forward. -/
def appendCommand (before after : Runtime) (command : Command) (report : Report)
    (identifier : Nat) : Except String Runtime := do
  let event : History.Event Nat Nat :=
    { identifier := identifier, patch :=
      [{ key := 0, before := before.incumbent.id, after := after.incumbent.id },
       { key := 1, before := before.contract.context, after := after.contract.context }] }
  let submitted := match command with
    | .undo _ source =>
        if report.accepted then History.undoRecorded before.journal source identifier
        else History.submit before.journal event
    | _ => History.submit before.journal event
  let some journal := submitted |
    throw "journal guard refused the command; no state was committed"
  pure { after with
    journal := journal,
    receipts := before.receipts ++ [⟨command, report⟩] }

def process (state : Runtime) (command : Command) : Except String (Runtime × Report) := do
  match command.identifier with
  | none =>
      let (next, report) ← runFresh state command
      pure ({ next with
        totalEvaluated := state.totalEvaluated + report.evaluated,
        totalReused := state.totalReused + report.reused }, report)
  | some identifier =>
      match state.receipts.find? (fun receipt => receipt.command.identifier == some identifier) with
      | some prior =>
          if prior.command = command then
            pure (state, ⟨command.name, "replayed", prior.report.accepted, 0, 0⟩)
          else pure (state, ⟨command.name, "conflict-refused", false, 0, 0⟩)
      | none =>
          let (next, report) ← runFresh state command
          let next ← appendCommand state next command report identifier
          pure ({ next with
            totalEvaluated := state.totalEvaluated + report.evaluated,
            totalReused := state.totalReused + report.reused }, report)

def reportJson (state : Runtime) (report : Report) : String :=
  "{" ++ String.intercalate "," [
    "\"op\":\"" ++ report.op ++ "\"",
    "\"status\":\"" ++ report.status ++ "\"",
    "\"accepted\":" ++ toString report.accepted,
    "\"context\":" ++ toString state.contract.context,
    "\"incumbent\":" ++ toString state.incumbent.id,
    "\"archive\":" ++ toString state.archive.length,
    "\"observations\":" ++ toString state.observations.length,
    "\"journal_events\":" ++ toString state.journal.events.length,
    "\"evidence_entries\":" ++ toString state.cache.length,
    "\"evaluated\":" ++ toString report.evaluated,
    "\"reused\":" ++ toString report.reused,
    "\"total_evaluated\":" ++ toString state.totalEvaluated,
    "\"total_reused\":" ++ toString state.totalReused] ++ "}"

def execute (scenario : Scenario) : Except String (List String) := do
  let (state, report) ← startScenario scenario
  let rec go (state : Runtime) (remaining : List Command) (lines : List String) :
      Except String (List String) := do
    match remaining with
    | [] => pure lines.reverse
    | command :: tail =>
        let (next, report) ← process state command
        go next tail (reportJson next report :: lines)
  go state scenario.commands [reportJson state report]

def main (args : List String) : IO UInt32 := do
  let [path] := args |
    IO.eprintln "usage: dynamic <scenario.json>"
    return 1
  let text ← IO.FS.readFile path
  let some scenario := parse text |
    IO.eprintln "invalid dynamic scenario JSON or schema"
    return 1
  match execute scenario with
  | .error message =>
      IO.eprintln message
      return 1
  | .ok lines =>
      for line in lines do IO.println line
      return 0

end DynamicCli

def main : List String → IO UInt32 := DynamicCli.main
