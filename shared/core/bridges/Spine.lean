-- variant: theses/is-quantifiable SoftwareIsQuantifiable.Spine.Core
import SoftwareCore
import SoftwareIsQuantifiable.Spine.Core

namespace SoftwareCore.Bridge.Spine
open _root_.SoftwareIsQuantifiable.Spine (State Rule)

theorem closed_iff (s : State) :
    _root_.SoftwareIsQuantifiable.Spine.Closed s ↔
      SoftwareCore.Closed (SoftwareCore.ofRecords Rule.premises Rule.conclusion s.rules)
        (fun x => x ∈ s.seeds) := by
  constructor
  · intro h ps a ⟨r, hr, hp, hc⟩ hps
    subst hp; subst hc
    exact h r hr hps
  · intro h r hr hps
    exact h _ _ ⟨r, hr, rfl, rfl⟩ hps

end SoftwareCore.Bridge.Spine
