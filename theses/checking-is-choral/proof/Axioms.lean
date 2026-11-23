/-
  The dependency audit for choral checking. Every main theorem and
  every control is printed with the foundational principles it
  depends on; the family gate fails if any printed principle lies
  outside the allowed set {propext, Classical.choice, Quot.sound}.
-/

import Choral
import Controls

open Choral

#print axioms fueleval
#print axioms wholefold
#print axioms conepoint
#print axioms joinediff
#print axioms auditpoint
#print axioms auditjoin
#print axioms Controls.boundarymatters
#print axioms Controls.covermatters
