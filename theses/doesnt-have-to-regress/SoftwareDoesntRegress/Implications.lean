import Lean
import SoftwareDoesntRegress.Policy
import SoftwareDoesntRegress.Boundary
import SoftwareDoesntRegress.Resolution
import SoftwareDoesntRegress.Baseline
import SoftwareDoesntRegress.ContextCone

open Lean

namespace SoftwareDoesntRegress

def headlines : Array Name := #[
  `SoftwareDoesntRegress.step_witness,
  `SoftwareDoesntRegress.shipped_chain,
  `SoftwareDoesntRegress.policy_exists,
  `SoftwareDoesntRegress.accepted_strict,
  `SoftwareDoesntRegress.accepts_complete,
  `SoftwareDoesntRegress.ascend_ships_of_exists,
  `SoftwareDoesntRegress.ascend_frontier,
  `SoftwareDoesntRegress.not_per_execution_dominance,
  `SoftwareDoesntRegress.accepted_not_per_execution,
  `SoftwareDoesntRegress.not_unobserved_nonregression,
  `SoftwareDoesntRegress.nonregression_if_coverage,
  `SoftwareDoesntRegress.not_every_gate_complete,
  `SoftwareDoesntRegress.complete_gate_decides,
  `SoftwareDoesntRegress.finer_bounds,
  `SoftwareDoesntRegress.finer_behaviors,
  `SoftwareDoesntRegress.finer_strict,
  `SoftwareDoesntRegress.coarse_admits_symbol_regression,
  `SoftwareDoesntRegress.baseline_is_witness,
  `SoftwareDoesntRegress.select_never_regresses,
  `SoftwareDoesntRegress.behaviorsKept_eq_composable,
  `SoftwareDoesntRegress.unchanged_symbol_context_recheck,
  `SoftwareDoesntRegress.ariane_symbol_only_misses,
  `SoftwareDoesntRegress.ariane_context_cone_catches,
  `SoftwareDoesntRegress.crowdstrike_symbol_only_misses,
  `SoftwareDoesntRegress.crowdstrike_data_cone_catches,
  `SoftwareDoesntRegress.knight_symbol_only_misses,
  `SoftwareDoesntRegress.knight_config_cone_catches,
  `SoftwareDoesntRegress.knight_deployment_cone_catches
]

def isUpstream (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "SoftwareIsQuantifiable" ||
    s.startsWith "Qualification" ||
    s.startsWith "ExecutableClosure" ||
    s.startsWith "FiniteFrontier" ||
    s.startsWith "FiniteSchedules" ||
    s.startsWith "SoftwareIsComposable" ||
    s.startsWith "SoftwareIsIncrementallyCertifiable"

def isOurs (n : Name) : Bool :=
  n.toString.startsWith "SoftwareDoesntRegress"

def constExprs (info : ConstantInfo) : Array Expr :=
  match info with
  | .thmInfo v => #[v.type, v.value]
  | .defnInfo v => #[v.type, v.value]
  | .opaqueInfo v => #[v.type, v.value]
  | _ => #[]

def used (e : Expr) : NameSet :=
  e.foldConsts {} fun n acc => acc.insert n

def isThm (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

def walk (env : Environment) (n : Name) (fuel : Nat) (seen : NameSet) (up : NameSet)
    (lems : NameSet) : NameSet × NameSet :=
  match fuel with
  | 0 => (up, lems)
  | fuel + 1 =>
    if seen.contains n then (up, lems)
    else
      match env.find? n with
      | none => (up, lems)
      | some info =>
        let seen := seen.insert n
        let consts : NameSet :=
          Array.foldl (fun (acc : NameSet) e => acc.union (used e)) {} (constExprs info)
        RBTree.fold (fun (acc : NameSet × NameSet) (c : Name) =>
          let (up, lems) := acc
          if c == n then (up, lems)
          else if isUpstream c then (up.insert c, lems)
          else if isOurs c then
            let lems := if c != n && isThm env c then lems.insert c else lems
            walk env c fuel seen up lems
          else (up, lems)) (up, lems) consts

def render (s : NameSet) : String :=
  let names := (s.toList.map Name.toString).mergeSort
  if names.isEmpty then "(none)" else String.intercalate ", " names

def implicationLines (env : Environment) : Array String :=
  headlines.map fun thm =>
    let (up, lems) := walk env thm 30 {} {} {}
    s!"IMPLICATION {thm}\nFROM {render up}\nPLUS {render (lems.erase thm)}"

end SoftwareDoesntRegress

open SoftwareDoesntRegress

#print axioms SoftwareDoesntRegress.step_witness
#print axioms SoftwareDoesntRegress.shipped_chain
#print axioms SoftwareDoesntRegress.policy_exists
#print axioms SoftwareDoesntRegress.accepted_strict
#print axioms SoftwareDoesntRegress.accepts_complete
#print axioms SoftwareDoesntRegress.ascend_ships_of_exists
#print axioms SoftwareDoesntRegress.ascend_frontier
#print axioms SoftwareDoesntRegress.not_per_execution_dominance
#print axioms SoftwareDoesntRegress.accepted_not_per_execution
#print axioms SoftwareDoesntRegress.not_unobserved_nonregression
#print axioms SoftwareDoesntRegress.nonregression_if_coverage
#print axioms SoftwareDoesntRegress.not_every_gate_complete
#print axioms SoftwareDoesntRegress.complete_gate_decides
#print axioms SoftwareDoesntRegress.finer_bounds
#print axioms SoftwareDoesntRegress.finer_behaviors
#print axioms SoftwareDoesntRegress.finer_strict
#print axioms SoftwareDoesntRegress.coarse_admits_symbol_regression
#print axioms SoftwareDoesntRegress.baseline_is_witness
#print axioms SoftwareDoesntRegress.select_never_regresses
#print axioms SoftwareDoesntRegress.behaviorsKept_eq_composable
#print axioms SoftwareDoesntRegress.unchanged_symbol_context_recheck
#print axioms SoftwareDoesntRegress.ariane_symbol_only_misses
#print axioms SoftwareDoesntRegress.ariane_context_cone_catches
#print axioms SoftwareDoesntRegress.crowdstrike_symbol_only_misses
#print axioms SoftwareDoesntRegress.crowdstrike_data_cone_catches
#print axioms SoftwareDoesntRegress.knight_symbol_only_misses
#print axioms SoftwareDoesntRegress.knight_config_cone_catches
#print axioms SoftwareDoesntRegress.knight_deployment_cone_catches
