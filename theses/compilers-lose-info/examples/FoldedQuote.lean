import Std

namespace FoldedQuote

-- Two independent source choices can give the same settled price.
structure Price where
  tariff : Nat
  shipping : Nat
  tariffImported : Bool
  shippingImported : Bool

def emitted (p : Price) := p.tariff + p.shipping
def provenance (p : Price) := (p.tariffImported, p.shippingImported)
def carry (p : Price) := (emitted p, provenance p)
def quote (a b : Bool) : Price := ⟨90,10,a,b⟩

theorem loss : ¬ ∃ recover : Nat → Bool × Bool, ∀ p, recover (emitted p) = provenance p := by
  rintro ⟨f,h⟩
  have a := h (quote false false)
  have b := h (quote true false)
  exact absurd (a.symm.trans b) (by decide)

-- At this same output even a freely chosen one-bit side channel is insufficient.
theorem one_bit_impossible (tag : Price → Bool) (read : Nat → Bool → Bool × Bool) :
    ¬ ∀ p, read (emitted p) (tag p) = provenance p := by
  intro h
  have a := h (quote false false)
  have b := h (quote true false)
  have c := h (quote false true)
  change read 100 _ = (false,false) at a
  change read 100 _ = (true,false) at b
  change read 100 _ = (false,true) at c
  cases ha : tag (quote false false) <;> cases hb : tag (quote true false) <;>
    cases hc : tag (quote false true) <;> simp_all

theorem two_bits_suffice (p : Price) : (carry p).1 = emitted p ∧ (carry p).2 = provenance p := ⟨rfl,rfl⟩
theorem four_origins : ([quote false false, quote false true, quote true false, quote true true].map
    carry).eraseDups.length = 4 := by decide

#eval ([quote false false, quote false true, quote true false, quote true true].map carry)
#print axioms loss
#print axioms one_bit_impossible
#print axioms two_bits_suffice
#print axioms four_origins
end FoldedQuote
