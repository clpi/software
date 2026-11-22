import SoftwareDoesntRegress.Profiles

namespace GateExe

inductive J where
  | num : Nat → J
  | str : String → J
  | arr : List J → J
  | obj : List (String × J) → J

abbrev Cs := List Char

def ws : Cs → Cs
  | [] => []
  | c :: cs => if c = ' ' || c = '\n' || c = '\t' || c = '\r' then ws cs else c :: cs

def parseNat : Cs → Option (Nat × Cs)
  | [] => none
  | c :: cs =>
    if c.isDigit then
      if c == '0' && (cs.headD ' ').isDigit then none
      else
      let rec go (n : Nat) : Cs → Nat × Cs
        | d :: rest =>
          if d.isDigit then go (n * 10 + (d.toNat - '0'.toNat)) rest else (n, d :: rest)
        | [] => (n, [])
      some (go (c.toNat - '0'.toNat) cs)
    else none

def parseString : Cs → Option (String × Cs)
  | '"' :: cs =>
    let rec go : Cs → Option (List Char × Cs)
      | '"' :: rest => some ([], rest)
      | c :: rest =>
        if c == '\\' || c.toNat < 32 then none
        else
        match go rest with
        | some (xs, rest) => some (c :: xs, rest)
        | none => none
      | [] => none
    match go cs with
    | some (xs, rest) => some (String.mk xs, rest)
    | none => none
  | _ => none

mutual
def parseValue : Nat → Cs → Option (J × Cs)
  | 0, _ => none
  | fuel + 1, cs =>
  let cs := ws cs
  match cs with
  | '"' :: _ =>
    match parseString cs with
    | some (s, rest) => some (.str s, rest)
    | none => none
  | '[' :: rest =>
    match parseArray fuel (ws rest) with
    | some (xs, rest) => some (.arr xs, rest)
    | none => none
  | '{' :: rest =>
    match parseObject fuel (ws rest) with
    | some (xs, rest) => some (.obj xs, rest)
    | none => none
  | _ =>
    match parseNat cs with
    | some (n, rest) => some (.num n, rest)
    | none => none

def parseArray : Nat → Cs → Option (List J × Cs)
  | 0, _ => none
  | fuel + 1, cs =>
  let cs := ws cs
  match cs with
  | ']' :: rest => some ([], rest)
  | _ =>
    match parseValue fuel cs with
    | none => none
    | some (v, rest) =>
      match ws rest with
      | ',' :: rest =>
        if (ws rest).head? == some ']' then none
        else
        match parseArray fuel rest with
        | some (vs, rest) => some (v :: vs, rest)
        | none => none
      | ']' :: rest => some ([v], rest)
      | _ => none

def parseObject : Nat → Cs → Option (List (String × J) × Cs)
  | 0, _ => none
  | fuel + 1, cs =>
  let cs := ws cs
  match cs with
  | '}' :: rest => some ([], rest)
  | _ =>
    match parseString cs with
    | none => none
    | some (k, rest) =>
      match ws rest with
      | ':' :: rest =>
        match parseValue fuel rest with
        | none => none
        | some (v, rest) =>
          match ws rest with
          | ',' :: rest =>
            if (ws rest).head? == some '}' then none
            else
            match parseObject fuel rest with
            | some (vs, rest) =>
              if vs.any (fun entry => entry.1 == k) then none
              else some ((k, v) :: vs, rest)
            | none => none
          | '}' :: rest => some ([(k, v)], rest)
          | _ => none
      | _ => none
end

def lookup (k : String) : List (String × J) → Option J
  | [] => none
  | (k', v) :: rest => if k == k' then some v else lookup k rest

def natList : J → Option (List Nat)
  | .arr xs => xs.mapM fun
      | .num n => some n
      | _ => none
  | _ => none

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
