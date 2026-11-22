# software-proofs-are-portable

Twin: a release artifact carrying its own certificate as a derived
part of the artifact itself, so checking the artifact and checking
its proof are one act with one hash.

- SPEC.md states the form, the instance, the verification, the
  premises, and what is not claimed.
- Twin.lean proves the construction's four results over an abstract
  digest: soundness, the transplant bound, the refusal, and — under
  the named separation premise — that a verifying transplant is the
  same artifact. All four depend on no axioms.
- twin.py is the reference build and verify; gate.py is the standing
  attack battery; check.sh is the whole gate (escape scan, cold Lean
  build, gate).
- instance/ carries the first issuance: the monotonic certification
  pipeline's first certificate (clpi/idol-eyes, earlier
  d29300b68502af4c303e3a226477f5f6532d445f, later
  d7e7b009e735334bb2cbcff25db41320450ab051), its subject tree archive,
  the earlier tree archive the transplant attack uses, the anchors,
  and the recorded gate run.

Claim discipline: the certificate is carried exactly as issued — its
reading is **not certified**, with solvability, reweightability, and
speed unmeasured and blocking. Twin binds that certificate to its
artifact so the reading cannot be flipped by editing the carried
file; it does not upgrade the reading. The detached form's fall to a
flag-edit forgery, and the twin form's refusal of the same forgery,
are both executed and recorded in SPEC.md and the gate output.
