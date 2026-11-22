import Lean
import SoftwareIsComposable

open Lean

def isLocalName : Name → Bool
  | .str p _ => p == `SoftwareIsComposable || isLocalName p
  | .num p _ => isLocalName p
  | .anonymous => false

def isUpstreamName : Name → Bool
  | .str p _ =>
      p == `SoftwareIsQuantifiable || p == `FiniteQualification || p == `FiniteFrontier ||
        p == `Qualification || p == `ExecutableClosure || p == `HypergraphIncremental ||
        isUpstreamName p
  | .num p _ => isUpstreamName p
  | .anonymous => false

def exprConsts (e : Expr) : List Name :=
  e.foldConsts [] fun n acc => if acc.contains n then acc else n :: acc

def constConsts (env : Environment) (n : Name) : List Name :=
  match env.find? n with
  | none => []
  | some ci =>
    let fromType := exprConsts ci.type
    let fromVal := match ci.value? with
      | some v => exprConsts v
      | none => []
    fromType.foldl (fun acc n => if acc.contains n then acc else n :: acc) fromVal

def walkLocal (fuel : Nat) (env : Environment) (seen : List Name) (stack : List Name) : List Name :=
  match fuel with
  | 0 => seen
  | fuel + 1 =>
    match stack with
    | [] => seen
    | n :: rest =>
      if seen.contains n then walkLocal fuel env seen rest
      else
        let kids := (constConsts env n).filter isLocalName
        walkLocal fuel env (n :: seen) (kids ++ rest)

def sortStrings (xs : List String) : List String :=
  xs.mergeSort

def joinComma (xs : List String) : String :=
  match xs with
  | [] => "none"
  | x :: xs => xs.foldl (fun acc y => acc ++ ", " ++ y) x

def lastComponent : Name → String
  | .str _ s => s
  | .num n _ => lastComponent n
  | .anonymous => ""

def noisy (n : Name) : Bool :=
  let s := lastComponent n
  s.startsWith "_" || s.startsWith "match" || s.startsWith "eq_" ||
    s == "mk" || s == "rec" || s == "recOn" || s == "casesOn" ||
    s == "noConfusion" || s == "noConfusionType"

def keepDecl (env : Environment) (n : Name) : Bool :=
  if noisy n then false else
    match env.find? n with
    | some (.thmInfo _) => true
    | some (.defnInfo _) => isUpstreamName n
    | some (.inductInfo _) => isUpstreamName n
    | _ => false

def reportLine (env : Environment) (headline : Name) : String :=
  let direct := constConsts env headline
  let locals := (direct.filter fun n => isLocalName n && n != headline && keepDecl env n).map Name.toString
  let cone := walkLocal 20000 env [headline] (direct.filter isLocalName)
  let upstream := cone.foldl (fun acc n =>
      (constConsts env n).foldl (fun acc r =>
        if isUpstreamName r && keepDecl env r && !acc.contains r.toString then r.toString :: acc else acc) acc)
      []
  s!"{headline} from {joinComma (sortStrings upstream)} + {joinComma (sortStrings locals)}"

def headlines : List Name := [
  `SoftwareIsComposable.scheduleSpace_finite,
  `SoftwareIsComposable.releaseAdmitted_iff,
  `SoftwareIsComposable.releaseAdmitted_trans,
  `SoftwareIsComposable.symbolVerdict_admitted_iff,
  `SoftwareIsComposable.qualifiedMono,
  `SoftwareIsComposable.qualifiedTrans,
  `SoftwareIsComposable.costNoRegression,
  `SoftwareIsComposable.costTrans,
  `SoftwareIsComposable.not_per_execution,
  `SoftwareIsComposable.moduleAdmission_compose,
  `SoftwareIsComposable.moduleAdmission_counterexample,
  `SoftwareIsComposable.evidence_remaining,
  `SoftwareIsComposable.not_repeated_observation_shrinks,
  `SoftwareIsComposable.not_disqualification_empties,
  `SoftwareIsComposable.determined_of_coverage,
  `SoftwareIsComposable.inClosure_iff_affected,
  `SoftwareIsComposable.incrementalRecheck_iff,
  `SoftwareIsComposable.not_recheck_seed_only,
  `SoftwareIsComposable.worse_refused,
  `SoftwareIsComposable.Legacy.incremental_monotone,
  `SoftwareIsComposable.Legacy.reaches_monotone,
  `SoftwareIsComposable.Legacy.reaches_outside_stable,
  `SoftwareIsComposable.Legacy.foldApply_eq_composeAll,
  `SoftwareIsComposable.Interaction.incremental_monotone_iff,
  `SoftwareIsComposable.Interaction.legacy_has_origin,
  `SoftwareIsComposable.Interaction.legacy_embeds,
  `SoftwareIsComposable.Interaction.no_interaction_iff_legacy,
  `SoftwareIsComposable.Interaction.reaches_simulation,
  `SoftwareIsComposable.Interaction.reaches_refinement,
  `SoftwareIsComposable.Interaction.reaches_monotone,
  `SoftwareIsComposable.Interaction.incremental_interactions_monotone,
  `SoftwareIsComposable.Interaction.safe_of_closed,
  `SoftwareIsComposable.Interaction.universal_safety_iff_closed,
  `SoftwareIsComposable.Interaction.safe_of_simulation,
  `SoftwareIsComposable.Interaction.safe_of_refinement,
  `SoftwareIsComposable.Interaction.safe_of_incremental,
  `SoftwareIsComposable.Interaction.reaches_transfer_outside,
  `SoftwareIsComposable.Interaction.reaches_outside_stable,
  `SoftwareIsComposable.Interaction.incremental_recheck_iff
]

elab "write_implications " path:str : command => do
  let env ← getEnv
  for n in headlines do
    if env.find? n |>.isNone then
      throwError "missing headline {n}"
  let body := String.intercalate "\n" (headlines.map (reportLine env))
  IO.FS.writeFile path.getString (body ++ "\n")

write_implications "build/implications.md"
