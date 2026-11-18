namespace SoftwareIsIncrementallySafe

inductive Verdict (α : Type) where
  | accept
  | refuse (symbol : α)
  deriving DecidableEq, Repr

structure ExecDelta where
  changed : List (String × List String)
  deps : List (String × String)
  inspect : List String
  symHigh : String → Bool
  obsHigh : String → Bool
  boundTime : Nat
  boundCompute : Nat

def check
    (_forbidden : List String)
    (_allow : String → List String)
    (_base : String → List String)
    (_d : ExecDelta) : Verdict String :=
  .accept

end SoftwareIsIncrementallySafe
