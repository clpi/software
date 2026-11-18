import Lean
import SoftwareDoesntNeedReview.Audit

open Lean Elab Command

def constsOf (e : Expr) : Array Name :=
  e.foldConsts (#[] : Array Name) fun n acc => acc.push n

def followName (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "SoftwareDoesntNeedReview" ||
    s.startsWith "_private.SoftwareDoesntNeedReview"

def chainName (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "SoftwareDoesntNeedReview.Chain." ||
    s.startsWith "SoftwareIsComposable."

partial def chase (env : Environment) (fuel : Nat) (stack : List Name)
    (seen : NameSet) (hits : Array Name) : Array Name :=
  match fuel, stack with
  | _, [] => hits
  | 0, _ => hits
  | fuel + 1, n :: rest =>
    if seen.contains n then
      chase env fuel rest seen hits
    else
      let seen := seen.insert n
      let hits := if chainName n then hits.push n else hits
      let more :=
        if followName n then
          match env.find? n with
          | some ci =>
            let fromTy := constsOf ci.type
            let fromVal := match ci.value? with
              | some v => constsOf v
              | none => #[]
            (fromTy ++ fromVal).toList
          | none => []
        else
          []
      chase env fuel (more ++ rest) seen hits

def renderOne (env : Environment) (thm : Name) : String :=
  let hits := chase env 20000 [thm] {} #[]
  let sorted := hits.qsort fun a b => a.toString < b.toString
  let deps :=
    if sorted.isEmpty then
      "DEP none"
    else
      String.intercalate "\n" (sorted.toList.map fun n => s!"DEP {n}")
  s!"THEOREM {thm}\n{deps}"

def headlines : Array Name := #[
  `SoftwareDoesntNeedReview.RubberStamp.zero_information,
  `SoftwareDoesntNeedReview.RubberStamp.veto_empties,
  `SoftwareDoesntNeedReview.RubberStamp.agrees_or_pure_veto,
  `SoftwareDoesntNeedReview.RubberStamp.constant_reject_is_veto,
  `SoftwareDoesntNeedReview.RubberStamp.guarded_independent_of_approval,
  `SoftwareDoesntNeedReview.profile_space_finite,
  `SoftwareDoesntNeedReview.decided_on_finite_space,
  `SoftwareDoesntNeedReview.profile_criterion_mechanizable,
  `SoftwareDoesntNeedReview.Mechanize.semantic_not_total_axis,
  `SoftwareDoesntNeedReview.Mechanize.semantic_stays_premise,
  `SoftwareDoesntNeedReview.Mechanize.approx_keeps_gap,
  `SoftwareDoesntNeedReview.Mechanize.approx_gap_named,
  `SoftwareDoesntNeedReview.Chain.Certifiable.extensive,
  `SoftwareDoesntNeedReview.Chain.Certifiable.extensive_equiv,
  `SoftwareDoesntNeedReview.Chain.Regress.regress_equiv,
  `SoftwareDoesntNeedReview.Chain.Safe.safe_equiv,
  `SoftwareDoesntNeedReview.Replacement.process_monotone,
  `SoftwareDoesntNeedReview.Replacement.process_terminates,
  `SoftwareDoesntNeedReview.Replacement.criterion_never_lost,
  `SoftwareDoesntNeedReview.Boundary.boundary_missed_by_certifier,
  `SoftwareDoesntNeedReview.Boundary.boundary_legacy_witness_insufficient,
  `SoftwareDoesntNeedReview.Boundary.boundary_roster_not_mediated,
  `SoftwareDoesntNeedReview.Boundary.boundary_no_platform_premise,
  `SoftwareDoesntNeedReview.Boundary.residual_unwatched_cell,
  `SoftwareDoesntNeedReview.Boundary.outside_not_through_facts,
  `SoftwareDoesntNeedReview.Boundary.bad_cell_not_qualified,
  `SoftwareDoesntNeedReview.Boundary.redundant_under_premises,
  `SoftwareDoesntNeedReview.Boundary.redundant_on_unicodeBad,
  `SoftwareDoesntNeedReview.Boundary.empty_release_not_observed,
  `SoftwareDoesntNeedReview.Controls.control_before_misses,
  `SoftwareDoesntNeedReview.Controls.control_predicate_catches,
  `SoftwareDoesntNeedReview.Controls.control_after_refuses_by_name,
  `SoftwareDoesntNeedReview.Controls.control_predicate_is_finite_table,
  `SoftwareDoesntNeedReview.Controls.control_human_approves,
  `SoftwareDoesntNeedReview.Controls.control_human_regression_refused,
  `SoftwareDoesntNeedReview.Controls.control_human_regression_equiv,
  `SoftwareDoesntNeedReview.Controls.control_incomplete_passes,
  `SoftwareDoesntNeedReview.Controls.safety_refused_by_name,
  `SoftwareDoesntNeedReview.Controls.safety_equiv,
  `SoftwareDoesntNeedReview.Chain.Quantifiable.coverage,
  `SoftwareDoesntNeedReview.Chain.Quantifiable.unrestricted_witness,
  `SoftwareDoesntNeedReview.Chain.Quantifiable.missing_empty,
  `SoftwareDoesntNeedReview.Chain.Optimality.acceptsGuarded_iff
]

elab "emit_deps" : command => do
  let env ← getEnv
  let mut blocks : Array String := #[]
  for thm in headlines do
    blocks := blocks.push (renderOne env thm)
  let text := String.intercalate "\n" blocks.toList
  liftIO <| IO.println text

emit_deps
