import SoftwareIsQuantifiable.Pareto

namespace SoftwareDoesntRegress

structure Bound where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

def Bound.ok (b : Bound) : Bool :=
  decide (b.lo ≤ b.hi)

def Bound.noWorse (inc cand : Bound) : Bool :=
  decide (cand.lo ≤ inc.lo) && decide (cand.hi ≤ inc.hi)

def Bound.strict (inc cand : Bound) : Bool :=
  decide (cand.lo < inc.lo) || decide (cand.hi < inc.hi)

def addBound (a b : Bound) : Bound where
  lo := a.lo + b.lo
  hi := a.hi + b.hi

structure Profile (β : Type) where
  behaviors : List β
  bounds : List Bound
  deriving DecidableEq, Repr

abbrev Release (β : Type) := List (Profile β)

def behaviorsKept {β : Type} [DecidableEq β] (inc cand : List β) : Bool :=
  SoftwareIsQuantifiable.Pareto.accepts inc cand

def newBehavior {β : Type} [DecidableEq β] (inc cand : List β) : Bool :=
  match cand with
  | [] => false
  | b :: bs => (!decide (b ∈ inc)) || newBehavior inc bs

def boundsOk : List Bound → Bool
  | [] => true
  | b :: bs => Bound.ok b && boundsOk bs

def boundsNoWorse : List Bound → List Bound → Bool
  | [], [] => true
  | i :: is, c :: cs => Bound.noWorse i c && boundsNoWorse is cs
  | _, _ => false

def boundsStrict : List Bound → List Bound → Bool
  | [], [] => false
  | i :: is, c :: cs => Bound.strict i c || boundsStrict is cs
  | _, _ => false

def zipAdd : List Bound → List Bound → List Bound
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => addBound a b :: zipAdd as bs

def profileNoRegress {β : Type} [DecidableEq β] (inc cand : Profile β) : Bool :=
  behaviorsKept inc.behaviors cand.behaviors &&
    boundsNoWorse inc.bounds cand.bounds

def releaseOk {β : Type} : Release β → Bool
  | [] => true
  | p :: ps => boundsOk p.bounds && releaseOk ps

def profileStrict {β : Type} [DecidableEq β] (inc cand : Profile β) : Bool :=
  newBehavior inc.behaviors cand.behaviors || boundsStrict inc.bounds cand.bounds

def noRegress {β : Type} [DecidableEq β] : Release β → Release β → Bool
  | [], [] => true
  | i :: is, c :: cs => profileNoRegress i c && noRegress is cs
  | _, _ => false

def strictGain {β : Type} [DecidableEq β] : Release β → Release β → Bool
  | [], [] => false
  | i :: is, c :: cs => profileStrict i c || strictGain is cs
  | _, _ => false

def accepts {β : Type} [DecidableEq β] (inc cand : Release β) : Bool :=
  releaseOk inc && releaseOk cand && noRegress inc cand && strictGain inc cand

def step {β : Type} [DecidableEq β] (inc cand : Release β) : Release β :=
  if accepts inc cand then cand else inc

def ascend {β : Type} [DecidableEq β] (inc : Release β) (candidates : List (Release β)) : Release β :=
  candidates.foldl step inc

def ascendFuel {β : Type} [DecidableEq β] : Nat → Release β → List (Release β) → Release β
  | 0, acc, _ => acc
  | _, acc, [] => acc
  | n + 1, acc, c :: cs => ascendFuel n (step acc c) cs

def shipped {β : Type} [DecidableEq β] (stream : Nat → Release β) : Nat → Release β
  | 0 => stream 0
  | n + 1 => step (shipped stream n) (stream (n + 1))

def alwaysKeep {β : Type} (inc _cand : Release β) : Release β :=
  inc

def firstRefusal {β : Type} [DecidableEq β] : List String → Release β → Release β → Option String
  | n :: ns, i :: is, c :: cs =>
    if profileNoRegress i c then firstRefusal ns is cs else some n
  | _, _, _ => none

def decision (names : List String) (inc cand : Release Nat) : String :=
  if accepts inc cand then "accept"
  else if noRegress inc cand && !strictGain inc cand then "refuse-equal"
  else
    match firstRefusal names inc cand with
    | some n => "refuse " ++ n
    | none => "refuse"

structure Pair (β : Type) where
  sym : Nat
  inc : Profile β
  cand : Profile β
  deriving DecidableEq, Repr

def fineInc {β : Type} (ps : List (Pair β)) : Release β :=
  ps.map fun p => p.inc

def fineCand {β : Type} (ps : List (Pair β)) : Release β :=
  ps.map fun p => p.cand

def tagBehaviors {β : Type} (i : Nat) (bs : List β) : List (Nat × β) :=
  bs.map fun b => (i, b)

def sumBounds : List (List Bound) → List Bound
  | [] => []
  | b :: bs =>
    match sumBounds bs with
    | [] => b
    | s => zipAdd b s

def aggregate {β : Type} (ps : List (Pair β)) (side : Pair β → Profile β) : Profile (Nat × β) :=
  match ps with
  | [] => { behaviors := [], bounds := [] }
  | p :: ps =>
    let head := side p
    let rest := aggregate ps side
    { behaviors := tagBehaviors p.sym head.behaviors ++ rest.behaviors
      bounds :=
        match ps with
        | [] => head.bounds
        | _ => zipAdd head.bounds rest.bounds }

def bucketCount : List Nat → Nat
  | [] => 0
  | k :: ks => Nat.max (k + 1) (bucketCount ks)

def updateNth {α : Type} (n : Nat) (f : α → α) : List α → List α
  | [] => []
  | a :: as =>
    match n with
    | 0 => f a :: as
    | n + 1 => a :: updateNth n f as

def fillBuckets {β : Type} (n : Nat) (blockOf : List Nat) (ps : List (Pair β)) :
    List (List (Pair β)) :=
  let empty := List.replicate n ([] : List (Pair β))
  go blockOf ps empty
where
  go : List Nat → List (Pair β) → List (List (Pair β)) → List (List (Pair β))
  | k :: ks, p :: ps, buckets => go ks ps (updateNth k (fun b => b ++ [p]) buckets)
  | _, _, buckets => buckets

def pairsOf {β : Type} (inc cand : Release β) : List (Pair β) :=
  go 0 inc cand
where
  go (i : Nat) : Release β → Release β → List (Pair β)
  | p :: ps, c :: cs => { sym := i, inc := p, cand := c } :: go (i + 1) ps cs
  | _, _ => []

def groupsOf {β : Type} (blockOf : List Nat) (inc cand : Release β) : List (List (Pair β)) :=
  fillBuckets (bucketCount blockOf) blockOf (pairsOf inc cand)

def coarsen {β : Type} (blockOf : List Nat) (release : Release β) : Release (Nat × β) :=
  let n := bucketCount blockOf
  let tagged := release.zipIdx
  let empty := List.replicate n ([] : List (Profile β × Nat))
  let buckets := go blockOf tagged empty
  buckets.map aggregateOne
where
  go : List Nat → List (Profile β × Nat) → List (List (Profile β × Nat)) →
      List (List (Profile β × Nat))
  | k :: ks, p :: ps, buckets => go ks ps (updateNth k (fun b => b ++ [p]) buckets)
  | _, _, buckets => buckets
  aggregateOne (ps : List (Profile β × Nat)) : Profile (Nat × β) :=
    match ps with
    | [] => { behaviors := [], bounds := [] }
    | (p, i) :: ps =>
      let rest := aggregateOne ps
      { behaviors := tagBehaviors i p.behaviors ++ rest.behaviors
        bounds :=
          match rest.bounds with
          | [] => p.bounds
          | _ => zipAdd p.bounds rest.bounds }

def exNames : List String := ["parse", "emit"]

def exInc : Release Nat :=
  [ { behaviors := [1], bounds := [{ lo := 10, hi := 10 }] }
  , { behaviors := [2], bounds := [{ lo := 10, hi := 10 }] } ]

def exPure : Release Nat :=
  [ { behaviors := [1], bounds := [{ lo := 10, hi := 10 }] }
  , { behaviors := [2], bounds := [{ lo := 12, hi := 12 }] } ]

def exEqual : Release Nat := exInc

def exTrade : Release Nat :=
  [ { behaviors := [1], bounds := [{ lo := 1, hi := 1 }] }
  , { behaviors := [2], bounds := [{ lo := 12, hi := 12 }] } ]

def exBetter : Release Nat :=
  [ { behaviors := [1, 3], bounds := [{ lo := 9, hi := 9 }] }
  , { behaviors := [2], bounds := [{ lo := 10, hi := 10 }] } ]

def exBlock : List Nat := [0, 0]

def gateInc : Release Nat :=
  [{ behaviors := [0], bounds := [{ lo := 10, hi := 20 }] }]

def gateCand : Release Nat :=
  [{ behaviors := [0], bounds := [{ lo := 8, hi := 18 }] }]

def baseExample : Release Nat :=
  [{ behaviors := [0], bounds := [{ lo := 1, hi := 1 }] }]

def betterExample : Release Nat :=
  [{ behaviors := [0], bounds := [{ lo := 0, hi := 0 }] }]

def observedInc : Release Nat :=
  [{ behaviors := [0], bounds := [{ lo := 10, hi := 10 }] }]

def observedCand : Release Nat :=
  [{ behaviors := [0], bounds := [{ lo := 9, hi := 9 }] }]

def trueBehaviorsInc : List Nat := [0, 1]

def trueBehaviorsCand : List Nat := [0]

def r0 : Release Nat := exInc

def r1 : Release Nat := exBetter

def r2 : Release Nat :=
  [ { behaviors := [1, 3], bounds := [{ lo := 1, hi := 1 }] }
  , { behaviors := [2], bounds := [{ lo := 14, hi := 14 }] } ]

def r3 : Release Nat := r1

def streamUniverse : List (Release Nat) := [r1, r2, r3]

end SoftwareDoesntRegress
