import Lean.Data.Json
import IncrementalCert.Check

open Lean

namespace Cli

def strList (j : Json) : Except String (List String) := do
  let arr ← j.getArr?
  arr.toList.mapM Json.getStr?

def parseSteps (j : Json) : Except String (List (String × List String)) := do
  let arr ← j.getArr?
  arr.toList.mapM fun step => do
    let name ← (← step.getObjVal? "name").getStr?
    let beh ← strList (← step.getObjVal? "behaviors")
    pure (name, beh)

def deltaOf (behaviors : List String) : IncrementalCert.Delta where
  changed := [("app", behaviors)]
  deps := []
  inspect := []
  symHigh := IncrementalCert.lowSym
  obsHigh := IncrementalCert.noObsHigh
  boundTime := 100
  boundCompute := 100
  submittedRequired := []
  submittedAllowed := []

def specCli : IncrementalCert.Spec where
  symbols := ["app"]
  deps := []
  symHigh := IncrementalCert.lowSym
  obsHigh := IncrementalCert.noObsHigh
  allow := fun _ => ["need", "ok"]
  boundTime := 4
  boundCompute := 4
  required := ["need"]
  allowed := ["need", "ok"]
  forb := []

def prevCli : IncrementalCert.Prev where
  base := fun
    | "app" => ["need"]
    | _ => []
  qualified := ["need"]

def run (steps : List (String × List String)) : IO UInt32 := do
  let mut c : IncrementalCert.Certificate := { spec := specCli, prev := prevCli }
  let mut code : UInt32 := 0
  let mut stop := false
  for step in steps do
    if stop then
      IO.println s!"{step.1}: not-applied"
    else
      let d := deltaOf step.2
      match IncrementalCert.check c.spec c.prev d with
      | .accept =>
        IO.println s!"{step.1}: accept"
        match IncrementalCert.cert c d with
        | some c' => c := c'
        | none => pure ()
      | .refuse symbol =>
        IO.println s!"{step.1}: refused {symbol}"
        code := 1
        stop := true
  return code

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | do
    IO.eprintln "usage: certify chain.json"
    return 1
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e =>
    IO.eprintln e
    return 1
  | .ok j =>
    match j.getObjVal? "steps" with
    | .error e =>
      IO.eprintln e
      return 1
    | .ok stepsJson =>
      match parseSteps stepsJson with
      | .error e =>
        IO.eprintln e
        return 1
      | .ok steps =>
        run steps

end Cli

def main := Cli.main
