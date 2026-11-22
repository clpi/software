/- Twin: proofs that travel with the artifact they certify.

The model is the construction in SPEC.md, stated over an abstract
digest. An artifact is its bytes. A certificate names the digest of
the one artifact it certifies, states a property of artifacts, and
carries the issuer's soundness: any artifact whose digest is the
named digest has the property. The issuer issues that field only for
the artifact it actually checked; the field is the certificate's
proof content, and it is part of the certificate, not a side record.

A twin carries an artifact and its certificate together. Verification
is one act: the carried certificate's named digest is the digest of
the carried artifact. Three results are proved:

- sound: verification of the combined artifact implies the certified
  property of the artifact alone.
- transplant: a certificate carried over a different artifact, where
  the genuine twin verifies, verifies only if the two artifacts share
  a digest.
- refused: under the same hypothesis, any artifact whose digest
  differs from the certified artifact's digest refuses with that
  certificate — no further premise.
- same: under one named premise — the digest separates the two
  artifacts in question, the finite-range form of the collision
  resistance premise SPEC.md names — a verifying transplant is the
  same artifact.

Nothing here proves a digest collision resistant; that is the named
premise, exactly as SPEC.md states it. -/

/-- An artifact is its bytes. -/
abbrev Artifact := List UInt8

/-- A certificate over an abstract digest: the digest it names, the
property it states, and the issuer's soundness for that digest. -/
structure Certificate (digest : Artifact → Nat) where
  target : Nat
  property : Artifact → Prop
  sound : ∀ a, digest a = target → property a

/-- A twin: an artifact and its certificate, carried together. -/
structure Twin (digest : Artifact → Nat) where
  artifact : Artifact
  cert : Certificate digest

/-- Verification: the carried certificate names the carried
artifact's digest. -/
def Verified (digest : Artifact → Nat) (t : Twin digest) : Prop :=
  digest t.artifact = t.cert.target

namespace Twin

/-- Verification of the combined artifact implies the certified
property of the artifact alone. -/
theorem sound (digest : Artifact → Nat) (t : Twin digest)
    (h : Verified digest t) : t.cert.property t.artifact :=
  t.cert.sound t.artifact h

/-- A transplant verifies only if the two artifacts share a digest. -/
theorem transplant (digest : Artifact → Nat) (t : Twin digest)
    (a' : Artifact) (hv : Verified digest t)
    (h : Verified digest ⟨a', t.cert⟩) : digest a' = digest t.artifact :=
  h.trans hv.symm

/-- A different-digest artifact refuses with the genuine
certificate. -/
theorem refused (digest : Artifact → Nat) (t : Twin digest)
    (a' : Artifact) (hv : Verified digest t)
    (hne : digest a' ≠ digest t.artifact) :
    ¬ Verified digest ⟨a', t.cert⟩ :=
  fun h => hne (transplant digest t a' hv h)

/-- Under the separation premise for the pair in question, a
verifying transplant is the same artifact. -/
theorem same (digest : Artifact → Nat) (t : Twin digest)
    (a' : Artifact) (hv : Verified digest t)
    (h : Verified digest ⟨a', t.cert⟩)
    (sep : digest a' = digest t.artifact → a' = t.artifact) :
    a' = t.artifact :=
  sep (transplant digest t a' hv h)

end Twin
