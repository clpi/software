import Std

namespace RangeLedger.CertificateReuse
abbrev World := Nat → Int
def total (p : World) (a b : Nat) := p b - p a
def update (p displacement : World) : World := fun i => p i + displacement i

theorem exact_reuse (p displacement : World) (a b : Nat) :
    total (update p displacement) a b = total p a b ↔ displacement a = displacement b := by
  simp only [total,update]; omega

-- A +7 sample correction followed later by -7 gives a rectangular prefix displacement.
def correction (i : Nat) : Int := if 100 < i ∧ i ≤ 200 then 7 else 0
def pages := [(0,64),(64,128),(128,192),(192,256),(256,320),(320,384),(384,448),(448,512)]
def stale := pages.filter (fun (a,b) => correction a != correction b)
theorem affected : stale = [(64,128),(192,256)] ∧ correction 0 = correction 512 := by decide
theorem minimal (p : World) (a b : Nat) (h : (a,b) ∈ stale) :
    total (update p correction) a b ≠ total p a b := by
  have ne : correction a ≠ correction b := by simpa [stale] using (List.mem_filter.mp h).2
  exact fun eq => ne ((exact_reuse p correction a b).mp eq)
#eval stale
#print axioms exact_reuse
#print axioms minimal
#print axioms affected
end RangeLedger.CertificateReuse
