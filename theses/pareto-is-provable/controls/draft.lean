import Pareto

/- Control specimen for the obligation 3 hypothesis audit.
   This draft states finiteness as a hypothesis. The audit must
   detect it and refuse it. It is never part of the proof: the
   gate does not compile it, and the audit run over it must
   exit nonzero. -/

theorem draft (s : space) (h : fin (· ∈ s.cands)) : True :=
  trivial
