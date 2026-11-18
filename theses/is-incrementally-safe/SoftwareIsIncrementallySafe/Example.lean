import SoftwareIsIncrementallySafe.Checker

namespace SoftwareIsIncrementallySafe

def evilDelta : ExecDelta where
  changed := [("unsafe_exec", ["spawn"])]
  deps := []
  inspect := ["unsafe_exec"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10

example :
    check ["unsafe_exec"] (fun _ => []) (fun _ => []) evilDelta =
      Verdict.refuse "unsafe_exec" := by
  decide

theorem evil_refused :
    check ["unsafe_exec"] (fun _ => []) (fun _ => []) evilDelta =
      Verdict.refuse "unsafe_exec" := by
  decide

def benignDelta : ExecDelta where
  changed := [("logger", ["write"])]
  deps := []
  inspect := ["logger"]
  symHigh := fun _ => false
  obsHigh := fun _ => false
  boundTime := 10
  boundCompute := 10

theorem benign_accepted :
    check [] (fun _ => ["write"]) (fun _ => []) benignDelta = Verdict.accept := by
  decide

#eval check ["unsafe_exec"] (fun _ => []) (fun _ => []) evilDelta

end SoftwareIsIncrementallySafe
