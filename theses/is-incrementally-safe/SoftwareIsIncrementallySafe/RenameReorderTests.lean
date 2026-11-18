import SoftwareIsIncrementallySafe.RenameReorder

open SoftwareIsQuantifiable.Interface

namespace SoftwareIsIncrementallySafe
namespace RenameReorderTests

open RenameReorder

example {Prog Binder Digest Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure)
    (rename : Renaming Binder → Prog → Prog) (digest : Prog → Digest)
    (equiv : Prog → Prog → Prop) (profileOf : Prog → Release Symbol Measure) :
    RenameZeroDelta space rename digest equiv profileOf :=
  renameZeroDelta space rename digest equiv profileOf

example {Effect Prog Digest Symbol Measure : Type} [DecidableEq Symbol]
    (space : MeasureSpace Measure)
    (commutes : Effect → Effect → Prop) (ctx : Effect → Effect → Prog)
    (digest : Prog → Digest) (profileOf : Prog → Release Symbol Measure) :
    CommutingReorderZeroDelta space commutes ctx digest profileOf :=
  commutingReorderZeroDelta space commutes ctx digest profileOf

example : RenameNeedsDigestRenameInvariant := renameNeedsDigestRenameInvariant
example : RenameNeedsDigestCollisionFree := renameNeedsDigestCollisionFree
example : RenameNeedsProfileRespects := renameNeedsProfileRespects
example : ReorderNeedsEffectAlgebraSound := reorderNeedsEffectAlgebraSound
example : ReorderNeedsDigestOrderOnlyIfCommutes := reorderNeedsDigestOrderOnlyIfCommutes
example : NonCommutingChangesProfile := nonCommutingChangesProfile
example : UnorderedDigestUnsound := unorderedDigestUnsound

end RenameReorderTests
end SoftwareIsIncrementallySafe
