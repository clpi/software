import SoftwareIsIncrementallySafe.AuditFix
import SoftwareIsIncrementallySafe.RunAdmission

namespace SoftwareIsIncrementallySafe.FullSnapshotAudit

def noChange : ExecDelta := { omittedDelta with changed := [] }

theorem unsafe_baseline_refused :
    check appSpec (fun _ => ["not-allowed"]) noChange = .refuse "app" := by decide

theorem missing_required_baseline_refused :
    check liveSpec (fun _ => []) noChange = .refuse "lib" := by decide

def forbiddenParent : RepoSpec := { appSpec with
  allow := fun _ => ["net"]
  forbidden := ["app"] }

theorem transitive_forbidden_refused :
    check forbiddenParent (fun _ => []) omittedDelta = .refuse "app" := by decide

def duplicateUpdate : ExecDelta := { omittedDelta with changed := [("lib", []), ("lib", ["net"])] }
theorem duplicate_refused : check appSpec (fun _ => []) duplicateUpdate = .refuse "lib" := by decide

def unknownUpdate : ExecDelta := { omittedDelta with changed := [("unknown", [])] }
theorem unknown_refused : check appSpec (fun _ => []) unknownUpdate = .refuse "unknown" := by decide

def badEndpoints : RepoSpec := { appSpec with deps := [("app", "outside")] }
theorem malformed_graph_refused : check badEndpoints (fun _ => []) noChange = .refuse "<snapshot>" := by decide

def lawfulCycle : RepoSpec := { appSpec with
  deps := [("app", "lib"), ("lib", "app")]
  allow := fun _ => ["net"] }
theorem cyclic_lawful_accepted : check lawfulCycle (fun _ => []) omittedDelta = .accept := by decide

def retainedBaseline : String → List String := fun x => if x == "lib" then ["serve"] else []
theorem required_retained_accepted : check liveSpec retainedBaseline noChange = .accept := by decide

def changedPolicyOnly : RepoSpec := { liveSpec with required := fun _ => ["new"] }
theorem policy_change_rechecks_baseline :
    check changedPolicyOnly retainedBaseline noChange = .refuse "lib" := by decide

/-- NodeKind remains metadata. Every represented node receives the same checks;
this does not prove an external config/data extractor's completeness. -/
theorem node_kind_does_not_bypass :
    check { appSpec with kind := fun _ => .data } (fun _ => []) omittedDelta = .refuse "app" := by decide

#print axioms accepted_envelope
#print axioms accepted_reachability
#print axioms accepted_required
#print axioms accepted_forbidden_no_reaches
#print axioms check_submitter_invariant

end SoftwareIsIncrementallySafe.FullSnapshotAudit
