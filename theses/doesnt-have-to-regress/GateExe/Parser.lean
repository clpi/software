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

end GateExe
