-- variant: theses/frontier-is-solvable Canon
-- Also covers the byte-identical copy theses/redundant-compute-expands/proof/Canon.lean.
import SoftwareCore
import Canon

namespace SoftwareCore.Bridge.Canon
universe u
variable {A : Type u}

theorem derives_iff (B : A → Prop) (R : List A → A → Prop) (a : A) :
    _root_.Canon.Derives B R a ↔ SoftwareCore.Derives B R a := by
  constructor
  · intro d; induction d with
    | root hb => exact .root hb
    | step hr _ ih => exact .step hr ih
  · intro d; induction d with
    | root hb => exact .root hb
    | step hr _ ih => exact .step hr ih

theorem hypergraph_derives_iff (g : _root_.Canon.Hypergraph A) (a : A) :
    _root_.Canon.derives g a ↔ SoftwareCore.Derives g.roots g.edges a :=
  derives_iff g.roots g.edges a

end SoftwareCore.Bridge.Canon
