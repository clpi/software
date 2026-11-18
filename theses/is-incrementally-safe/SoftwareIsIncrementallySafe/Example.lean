import SoftwareIsIncrementallySafe.Checker

namespace SoftwareIsIncrementallySafe

def evilSpec : RepoSpec where
  deps := []
  allow := fun _ => []
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10
  required := fun _ => []
  obsCost := fun _ => 1
  forbidden := ["unsafe_exec"]
  kind := fun _ => .code

def evilDelta : ExecDelta where
  changed := [("unsafe_exec", ["spawn"])]
  deps := []
  inspect := ["unsafe_exec"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10

theorem evil_refused :
    check evilSpec (fun _ => []) evilDelta = Verdict.refuse "unsafe_exec" := by
  decide

def benignSpec : RepoSpec where
  deps := []
  allow := fun _ => ["write"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10
  required := fun _ => []
  obsCost := fun _ => 1
  forbidden := []
  kind := fun _ => .code

def benignDelta : ExecDelta where
  changed := [("logger", ["write"])]
  deps := []
  inspect := ["logger"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10

theorem benign_accepted :
    check benignSpec (fun _ => []) benignDelta = Verdict.accept := by
  decide

#eval check evilSpec (fun _ => []) evilDelta

#print axioms evil_refused
#print axioms benign_accepted

end SoftwareIsIncrementallySafe
