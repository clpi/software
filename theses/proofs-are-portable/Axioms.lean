/- Axiom audit: the kernel prints the axioms each headline result
depends on. The family gate reads this output in the build log.
Expected, for every line: only the standard axioms
(propext, Classical.choice, Quot.sound), and no other. -/

import Twin

#print axioms Twin.sound
#print axioms Twin.transplant
#print axioms Twin.refused
#print axioms Twin.same
