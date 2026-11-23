import GateExe.Parser

namespace GateExe

def boundOf : J → Option SoftwareDoesntRegress.Bound
  | .arr [.num lo, .num hi] => some { lo := lo, hi := hi }
  | _ => none

def profileOf : J → Option (SoftwareDoesntRegress.Profile Nat)
  | .obj fs => do
      let b ← lookup "behaviors" fs
      let u ← lookup "bounds" fs
      let behaviors ← natList b
      let bounds ← match u with
        | .arr xs => xs.mapM boundOf
        | _ => none
      pure { behaviors := behaviors, bounds := bounds }
  | _ => none

def releaseOf : J → Option (String × SoftwareDoesntRegress.Release Nat)
  | .obj fs => do
      let name ← match lookup "name" fs with
        | some (.str s) => pure s
        | _ => none
      let symbols ← match lookup "symbols" fs with
        | some (.arr xs) => xs.mapM profileOf
        | _ => none
      pure (name, symbols)
  | _ => none

def parseFile (cs : Cs) : Option (List String × List (String × SoftwareDoesntRegress.Release Nat)) := do
  let (v, rest) ← parseValue (cs.length * 3 + 1) cs
  if ws rest ≠ [] then none
  else
    match v with
    | .obj fs => do
        let names ← match lookup "names" fs with
          | some (.arr xs) => xs.mapM fun
              | .str s => pure s
              | _ => none
          | _ => none
        let releases ← match lookup "releases" fs with
          | some (.arr xs) => xs.mapM releaseOf
          | _ => none
        pure (names, releases)
    | _ => none

def run (names : List String)
    (releases : List (String × SoftwareDoesntRegress.Release Nat)) : List String :=
  match releases with
  | [] => []
  | (n0, r0) :: rest =>
    let rec go (incName : String) (inc : SoftwareDoesntRegress.Release Nat)
        (rest : List (String × SoftwareDoesntRegress.Release Nat)) (acc : List String) : List String :=
      match rest with
      | [] => if incName.isEmpty then acc.reverse else acc.reverse
      | (n, r) :: rest =>
        let accepted := SoftwareDoesntRegress.accepts inc r
        let shipped := SoftwareDoesntRegress.step inc r
        let shipName := if accepted then n else incName
        let line := s!"{n} {SoftwareDoesntRegress.decision names inc r} ship {shipName}"
        go shipName shipped rest (line :: acc)
    go n0 r0 rest [s!"{n0} ship {n0}"]

def main (args : List String) : IO UInt32 := do
  let some path := args.head? |
    IO.eprintln "usage: gate <stream.json>"
    return 1
  let text ← IO.FS.readFile path
  match parseFile text.toList with
  | none =>
    IO.eprintln "invalid stream"
    return 1
  | some (names, releases) =>
    for line in run names releases do
      IO.println line
    return 0

end GateExe

def main : List String → IO UInt32 :=
  GateExe.main
