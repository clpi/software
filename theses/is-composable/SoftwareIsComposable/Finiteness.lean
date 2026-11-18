import SoftwareIsQuantifiable.Finiteness

namespace SoftwareIsComposable

theorem scheduleSpace_finite (q : SoftwareIsQuantifiable.Finiteness.Qualification Nat Nat) :
    ∃ L : List (SoftwareIsQuantifiable.Finiteness.Schedule Nat Nat),
      ∀ s, SoftwareIsQuantifiable.Finiteness.Valid q s → s ∈ L :=
  SoftwareIsQuantifiable.Finiteness.valid_orderings_finite q

end SoftwareIsComposable
