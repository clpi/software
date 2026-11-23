# Twin — proofs that travel with the artifact they certify

## The claim

A release artifact can carry its own certificate as a derived part of
the artifact itself, so that checking the artifact and checking its
proof are one act with one hash, and a forged or detached certificate
cannot verify against a different artifact.

Certificates in the estate are issued beside artifacts, as separate
records. The forged qualification flag attack of 2026-11-20 (record:
~/workspace/research/c-demo-disposition-2026-11-20.md, claim 8) showed
the class this closes: a detached flag, flipped by whoever holds the
file, admitted an unqualified action. Section 1 below demonstrates the
same class on this item's own instance before the construction is
stated: the detached certificate's own checker accepts a forgery made
of flag edits alone.

## The instance

The one certified release transition in the estate: the monotonic
certification pipeline's first issuance, in
clpi/software-certification-is-monotone at
4539760e0589fdcb3327d7b6ded90bb71af3a808.

- Subject: clpi/idol-eyes.
- Earlier pin: d29300b68502af4c303e3a226477f5f6532d445f.
- Later pin: d7e7b009e735334bb2cbcff25db41320450ab051.
- The artifact: the subject tree at the later pin, as the archive
  `git archive` produces for that pin (instance/artifact.tar).
- The certificate: the issued certificate file, byte for byte
  (instance/cert.json).
- The property the certificate carries, exactly as issued: the
  transition is consistent under the issuer's reading rule, no
  dimension regressed, and the reading is **not certified** —
  solvability, reweightability, and speed stand unmeasured and block
  certification. Twin carries the certificate as issued. It does not
  upgrade the reading, and no twin verification of this instance
  accepts a certified reading.

Anchors, recorded at issuance in instance/manifest.json and here;
each is re-derivable from the pinned repos named above:

- artifact digest (sha256 of instance/artifact.tar):
  30a96f72695b41753a768496b5a81b27f4c4cdb5758a6790616468aaae39cfbc
- issued certificate digest (sha256 of instance/cert.json):
  b508d8a477e524e6d02cbb9e86ccdaaa915a9f18e92a85324d8e03157b90be52
- earlier tree archive digest (the transplant target):
  11d5d87f1deae6fdebc85db42c5fa5c3576d58b7d8f14d5d257d5cfb8ae2cf7d
- the issuer's checker (checker.py, a byte-identical copy of the
  issuing repo's checker at the pin above), sha256:
  775c5f38a94e7ba4d1b5d532878e86bac7f37adcbb7c0e9df29201bf4dfc7446

The twin bundle built from this instance has digest
7edff531331f587dd79029bfe0ece48ff331f3d1852166dd94b30b8ba424121e —
the one hash that names the artifact and its proof together.

## 1. The detached form falls (executed control)

The issuer's checker, run over the issued certificate, prints
CONSISTENT and exits 0. The same checker, run over a copy whose three
unmeasured dimensions are flipped to flat with fabricated values,
fabricated coverage text, and fabricated evidence strings, and whose
reading is flipped to certified, also prints CONSISTENT and exits 0,
with the recomputed reading "certified". The checker verifies
internal consistency only; nothing in the detached form binds the
certificate to the subject trees or to what the issuer actually
issued, so flag edits alone manufacture a certified reading. This is
the forged-flag class on this artifact, reproduced firsthand at the
pins above on 2026-11-21.

## 2. The form

One bundle file (twin.py is the reference build and verify):

- a fixed magic line;
- a length-prefixed manifest in canonical JSON, naming the subject,
  the two pins, the reading as issued, the artifact digest, the
  certificate digest, a binding digest computed over the two digests,
  and the two component lengths — the manifest's field names stand as
  they are written in twin.py, which is their home;
- the artifact bytes;
- the certificate bytes;
- nothing else: trailing bytes refuse the bundle.

Assembly is not issuance and is not verification. The builder is a
dumb assembler over whatever pair it is handed, and gate.py hands it
attack pairs on purpose. Verification is the binding act.

## 3. Verification

One command (twin.py, verify) over one bundle:

1. Parse; refuse truncation or trailing bytes.
2. Recompute the artifact digest and the certificate digest from the
   carried bytes; refuse any mismatch with the manifest.
3. Recompute the binding digest; refuse any mismatch.
4. Refuse unless the certificate digest equals the anchored issued
   digest and the artifact digest equals the anchored certified
   digest. The anchors are the digests in section "The instance",
   derived from the pinned repos; they are verification's inputs, not
   fields the bundle can carry about itself.
5. Refuse unless the certificate's own subject, pins, and reading
   match the manifest.
6. Run the issuer's standing checker over the carried certificate;
   refuse unless it accepts (CONSISTENT) and its recomputed reading
   equals the reading as issued.

Accept prints the reading as issued and the bundle digest. Every
refusal names its step.

## 4. What is proved

Twin.lean, over an abstract digest, gate cold, warnings as errors,
no escape tokens. All four results depend on no axioms at all
(Axioms.lean prints the audit; the build log carries it):

- sound: verification of the combined artifact implies the certified
  property of the artifact alone.
- transplant: where the genuine twin verifies, a transplant of its
  certificate over a different artifact verifies only if the two
  artifacts share a digest.
- refused: under the same hypothesis, an artifact whose digest
  differs refuses with that certificate — no further premise.
- same: under the separation premise for the pair in question, a
  verifying transplant is the same artifact.

Premises, named and not proved here:

- Collision resistance: the digest separates distinct artifacts on
  the byte ranges in question. Twin.same takes this as an explicit
  hypothesis for the pair it speaks about; Twin.refused needs only
  digest inequality, which the verifier computes. SHA-256 is the
  digest the instance uses; its collision resistance is assumed, in
  the open, exactly as the register's proof route names it.
- The underlying certificate is valid as issued: the issuing
  pipeline's own soundness results stand in its repo at its pin, and
  the reading carried is the reading it issued — not certified, with
  its three blockers named.

## 5. The gate

check.sh runs the escape scan, the cold Lean build, and gate.py.
gate.py runs six checks and fails closed on the first disagreement:
determinism (two builds byte-identical), honest (the instance bundle
verifies, reading as issued), flip in the artifact (refused), flip in
the certificate (refused), transplant onto the earlier tree
(refused), and the section-1 forgery assembled over the genuine
artifact (refused). The recorded run is instance/gate-output.txt.

## 6. What is not claimed

- No issuer authentication beyond the anchored digests. Anyone can
  assemble a bundle; only a bundle whose components hash to the
  anchored digests verifies. Whoever can rewrite the anchors
  themselves — the pinned repos and this spec — is outside the
  construction's scope, as with every pin-anchored check in the
  estate.
- The archive bytes of a tree at a pin are whatever the archiving
  tool produces; the anchor is the digest, and the digest recorded
  here was reproduced from two independent archivings of the same
  pin with identical output. A different archiver producing
  different bytes for the same tree would carry a different anchor
  and would need its own issuance.
- The remaining six releases of Gate 3 are not re-issued here. This
  instance is the construction's first issuance; re-issuing the rest
  is the development route's next step, not a result of this repo.
