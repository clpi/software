import Std

namespace InvoiceTrace
inductive Event where | override | signature | quote | tax | currency | email | index | metrics
  deriving DecidableEq, Repr
inductive Route where | overridePath | pricingPath deriving DecidableEq, Repr
open Event Route
def journal := [email,quote,tax,override,index,signature,currency,metrics]
def needs : Route → List Event
  | overridePath => [override,signature]
  | pricingPath => [quote,tax,currency]
def supported (r : Route) (events : List Event) := (needs r).all events.contains
def evidence (r : Route) (events : List Event) := events.filter (fun e => (needs r).contains e)

theorem extraction_exact (r : Route) (events : List Event) (e : Event) :
    e ∈ evidence r events ↔ e ∈ events ∧ e ∈ needs r := by simp [evidence]

theorem preserves_verdict (r : Route) (events : List Event) :
    supported r (evidence r events) = supported r events := by
  apply Bool.eq_iff_iff.mpr
  simp [supported, List.all_eq_true, extraction_exact]
  exact ⟨fun h x hx => (h x hx).1, fun h x hx => ⟨h x hx,hx⟩⟩

theorem least_support (r : Route) (alt : List Event) (ok : supported r alt = true) :
    ∀ e ∈ evidence r journal, e ∈ alt := by
  intro e he
  simp [supported,List.all_eq_true] at ok
  exact ok e ((extraction_exact r journal e).mp he).2

theorem before_after : journal.length = 8 ∧ evidence overridePath journal = [override,signature] ∧
    evidence pricingPath journal = [quote,tax,currency] := by decide

-- Both produce the same visible approval; a route-free receipt cannot recover its premises.
theorem route_is_needed : ¬ ∃ f : Bool → List Event, ∀ r, f (supported r journal) = needs r := by
  rintro ⟨f,h⟩
  exact absurd ((h overridePath).symm.trans (h pricingPath)) (by decide)

#eval (journal.length, evidence overridePath journal, evidence pricingPath journal)
#print axioms extraction_exact
#print axioms preserves_verdict
#print axioms least_support
#print axioms before_after
#print axioms route_is_needed
end InvoiceTrace
