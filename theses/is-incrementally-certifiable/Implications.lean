import Lean
import IncrementalCert

open Lean

def nameLE (a b : Name) : Bool :=
  match Name.quickCmp a b with
  | .gt => false
  | _ => true

def isLocal (n : Name) : Bool :=
  (`IncrementalCert).isPrefixOf n || (`Audit).isPrefixOf n ||
    (`SoftwareIsComposable).isPrefixOf n

def isUpstream (n : Name) : Bool :=
  (`SoftwareIsComposable).isPrefixOf n || (`Qualification).isPrefixOf n ||
    (`FiniteQualification).isPrefixOf n || (`FiniteFrontier).isPrefixOf n ||
    (`ExecutableClosure).isPrefixOf n || (`HypergraphIncremental).isPrefixOf n ||
    (`SoftwareIsQuantifiable).isPrefixOf n || (`Optimality).isPrefixOf n ||
    (`CanonicalDominance).isPrefixOf n || (`FiniteFrontier).isPrefixOf n

elab "implications_report" : command => do
  let headlines : Array Name := #[
    `IncrementalCert.extensive,
    `IncrementalCert.monotone,
    `IncrementalCert.idempotent,
    `IncrementalCert.compounding,
    `IncrementalCert.evidence_cuts,
    `IncrementalCert.check_sound,
    `IncrementalCert.check_submitter_invariant,
    `IncrementalCert.incremental_eq_scratch,
    `IncrementalCert.pareto_monotone_chain,
    `IncrementalCert.outside_dominates,
    `IncrementalCert.coverage_gap_dominates,
    `IncrementalCert.axes_change_hides_regression,
    `IncrementalCert.not_per_execution,
    `IncrementalCert.combined_iff,
    `IncrementalCert.feature_add_fails_releaseLE,
    `IncrementalCert.removal_fails_acceptsRelease,
    `IncrementalCert.empty_required_passes_c4,
    `IncrementalCert.omitted_refused,
    `IncrementalCert.leak_unlabeled_refused,
    `IncrementalCert.budget_raised_refused,
    `IncrementalCert.nothing_refused,
    `IncrementalCert.required_is_prior,
    `IncrementalCert.allowed_is_spec,
    `IncrementalCert.check_ignores_spec_required,
    `IncrementalCert.empty_behaviors_refused,
    `IncrementalCert.spec_required_empty_still_refused,
    `IncrementalCert.submitted_required_still_refused,
    `IncrementalCert.unordered_traces,
    `IncrementalCert.profile_cannot_see_flow
  ]
  let env ← getEnv
  for id in headlines do
    let some ci := env.find? id | throwError s!"missing {id}"
    let names := ci.getUsedConstantsAsSet.toList.mergeSort nameLE
    let ups := names.filter isUpstream
    let loc := names.filter fun n => isLocal n && !isUpstream n && n != id
    IO.println ("THEOREM " ++ id.toString)
    IO.println ("  upstream: " ++ String.intercalate " " (ups.map toString))
    IO.println ("  local: " ++ String.intercalate " " (loc.map toString))

implications_report
