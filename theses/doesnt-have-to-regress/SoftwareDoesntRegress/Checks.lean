import SoftwareDoesntRegress.Profiles

namespace SoftwareDoesntRegress

#guard accepts exInc exPure == false
#guard firstRefusal exNames exInc exPure == some "emit"
#guard accepts exInc exEqual == false
#guard decision exNames exInc exEqual == "refuse-equal"
#guard accepts exInc exTrade == false
#guard firstRefusal exNames exInc exTrade == some "emit"
#guard accepts exInc exBetter == true
#guard accepts gateInc gateCand == true
#guard accepts baseExample betterExample == true
#guard accepts observedInc observedCand == true
#guard step r0 r1 == r1
#guard step r1 r2 == r1
#guard step r1 r3 == r1
#guard ascend r0 streamUniverse == r1
#guard accepts (coarsen exBlock exInc) (coarsen exBlock exTrade) == true
#guard decision exNames r1 r2 == "refuse emit"

end SoftwareDoesntRegress
