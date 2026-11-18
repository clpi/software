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

end SoftwareIsIncrementallySafe
