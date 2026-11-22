# Standing gate controls

Run `./check.sh` from any directory. Set `LEAN` to the pinned Lean executable
when it is not on `PATH`. The gate accepts no arguments and has no skip mode.

`scripts/check.py` discovers every repository `.lean` source recursively,
including orphan files, examples, and nested directories named `.lake` or
`build`. Only the root Git metadata and root Lake dependency/output directory
are excluded; a tracked Lean file hidden in those directories is rejected.
Sources and source directories may not be symlinks. Every discovered source
is independently compiled with warnings as errors into a fresh output directory.
Pinned dependency checkouts must be clean before and after checking, and their
build caches are cleared before the build.

The gate imports every compiled repository module and inspects every owned
declaration. It rejects every owned logical/custom axiom, then checks transitive
axiom dependencies of **every safe declaration**, including definitions and
generated propositions, against exactly `propext`, `Classical.choice`, and
`Quot.sound`. No unsafe runtime axiom may support any such declaration. Lean's
compiler-generated unsafe IO/Repr specializations are enumerated separately
in the log and receipt; they are not user-declared proof assumptions. The source
scanner separately refuses `unsafe`, `extern`, `implemented_by`, native proof
decisions, admitted proofs, environment injection operations, and unapproved
compiler options. Files containing ordinary string/message interpolation are
conservatively scanned in full, because interpolated bodies contain executable
Lean terms.

The existing `Implications.lean` elaborator reads the checked environment to
write a dependency report. Its exact source hash is the only admitted custom elaboration-hook exception.
It does not inject declarations or change checker options; other custom macros,
elaborators, initializers, and tactic hooks are rejected. The two existing example
files are also pinned by exact hash and may use `#eval` solely to display data;
new evaluation hooks are refused. Their proposition proofs are kernel checked
independently of displayed evaluation results. The gate and the pinned Lean toolchain remain part of the checking
trust boundary. This is a reproducible kernel check and escape scan, not a
claim that a repository can authenticate its own modified verifier.

The `.lean.fail` files are intentionally invalid controls, copied into temporary
files and required to fail; they are not proof modules. In particular,
`CharMask.lean.fail` prevents a regression in character-literal handling: the
double quote inside a Lean character must not hide a subsequent unsafe
declaration from the source scanner. `RawMask.lean.fail` checks the same boundary
for raw strings with explicit hash delimiters. `InterpolationMask.lean.fail`
contains a native proof decision inside a string interpolation; both the source
scanner and transitive declaration audit must refuse that escape.

Mandatory controls cover both admitted-proof spellings, orphan and nested custom axioms,
native decisions, kernel-check and warning-option bypasses, character, raw-string, and
quoted-identifier masking, unreviewed elaboration/evaluation hooks, source-directory symlinks, compiled custom axioms,
transitive imported custom axioms, warnings, a false admission theorem, and the
signed range-ledger mutation. The existing CSV harness output and release
partition example also have to match. A successful run writes source hashes,
gate-input hashes, dependency pins, declaration counts, toolchain identity, and
control results to `.lake/all-files-gate/receipt.json`.
