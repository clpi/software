import SoftwareIsComposable

open SoftwareIsComposable

def stripCR (s : String) : String :=
  s.replace "\r" ""

def parseNatList : List String → Option (List Nat)
  | [] => some []
  | s :: rest => do
    let n ← s.toNat?
    let ns ← parseNatList rest
    pure (n :: ns)

def parseBehaviors (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else parseNatList (s.splitOn " ")

def parseBound (s : String) : Option Bounds :=
  match s.splitOn ":" with
  | [lo, hi] => do
    let lo ← lo.toNat?
    let hi ← hi.toNat?
    pure { lo, hi }
  | _ => none

def parseCosts : List String → Option (List Bounds)
  | [] => some []
  | s :: rest => do
    let b ← parseBound s
    let bs ← parseCosts rest
    pure (b :: bs)

def parseCostField (s : String) : Option (List Bounds) :=
  if s.isEmpty then some [] else parseCosts (s.splitOn " ")

def parseProfile (line : String) : Option SymbolProfile :=
  match (stripCR line).splitOn "," with
  | [id, behaviors, costs] => do
    let id ← id.toNat?
    let behaviors ← parseBehaviors behaviors
    let costs ← parseCostField costs
    pure { id, behaviors, costs }
  | _ => none

def parseRelease (text : String) : Option Release := do
  let lines := (stripCR text).splitOn "\n"
  let mut symbols : List SymbolProfile := []
  for line in lines do
    if line.isEmpty || line == "id,behaviors,costs" then
      pure ()
    else
      let some p := parseProfile line | none
      symbols := symbols ++ [p]
  pure { symbols }

def renderReason : Reason → String
  | .missingSymbol _ => "missing_symbol"
  | .behaviorDropped _ b => s!"behavior_dropped {b}"
  | .costRegressed _ axis => s!"cost_regressed {axis}"
  | .axisMismatch _ => "axis_mismatch"
  | .invalidBounds _ => "invalid_bounds"

def renderRow : Nat × Verdict → String
  | (i, .admitted) => s!"{i} ADMITTED"
  | (i, .refused reason) => s!"{i} REFUSED {renderReason reason}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [oldPath, newPath] =>
    let oldText ← IO.FS.readFile oldPath
    let newText ← IO.FS.readFile newPath
    match parseRelease oldText, parseRelease newText with
    | some old, some new =>
      for row in symbolVerdicts old new do
        IO.println (renderRow row)
      return 0
    | _, _ =>
      IO.eprintln "parse error"
      return 2
  | _ =>
    IO.eprintln "usage: harness old.csv new.csv"
    return 2
