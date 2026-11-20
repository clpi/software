# Proof gate contract

Run `./check.sh` with the compiler from `lean-toolchain` on `PATH`, or set
`LEAN` to that compiler's absolute path. The script takes no bypass arguments.

The gate discovers every `.lean` file in the repository, including untracked
files, examples, and archival modules. Only the root `.git` and root `.lake`
metadata/build directories are excluded; nested directories with those names
are included. The build configuration is declarative `lakefile.toml`, avoiding
Lake DSL-generated configuration axioms inside the logical source audit. Source directory symlinks and
Lean file symlinks are rejected. The source scan removes nested comments and
strings before checking prohibited escapes and compiler-option changes.

Every discovered source is compiled freshly into an isolated build directory
with warnings treated as errors. Dependency repositories must be clean and at
the exact commits in `lake-manifest.json` before Lake executes dependency
configuration. Missing dependencies are fetched at those exact Git pins first.
Lake then builds the dependency closure. Dependency pins and cleanliness are
checked again after the proof and control runs. An independent recheck must use freshly rebuilt dependency artifacts;
matching a dependency's source pin alone is not an authentication of arbitrary
preexisting compiled caches.

The compiled-environment audit selects declarations by their originating module,
not a hard-coded theorem list or a namespace prefix. It checks every proof-valued
declaration, including anonymous examples and private helpers. It rejects every
safe custom axiom declaration, even if unused, and recursively rejects every
proof dependency outside Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. These three standard axioms are reported, never described as absent.

Lean generates unsafe runtime auxiliary declarations when compiling the existing
reporting elaborators. Unsafe declarations are counted separately as runtime
entries, not presumed to have trusted provenance merely from that flag. An unsafe
axiom with an inspectable proposition type is rejected. Runtime auxiliaries with
Lean compiler-only `_obj` types cannot be proposition-inspected; they remain
separately listed. Every accepted logical proof is still checked for prohibited
transitive assumptions. Explicit `unsafe`, `axiom`, and environment-mutation
escapes in source remain forbidden. The claim is zero custom logical proof
assumptions, not the absence of Lean runtime implementation declarations.

## Standing controls

- The historical admitted-proof fixture is `controls/Admitted.lean.fail`. It is
  both rejected by the escape scan and compiled in a temporary directory to
  confirm warnings-as-errors rejects it. There are no deliberately broken
  `.lean` files hidden from the all-files inventory.
- A newly created source in an unlisted directory must appear in the inventory,
  and its custom axiom must fail the scan. A separate file below a nested
  `.lake` directory must also be discovered and rejected.
- Native decision, kernel-check bypass, and warning-downgrade source controls
  must fail the escape scan. A source directory symlink must fail inventory.
- A compiled custom axiom and theorem that depends on it must fail the separate
  environment audit even when the source scan is bypassed for this control.
  A separate module importing that assumption must fail through transitive
  proof-dependency inspection when the defining module is outside the audit list.
- An unused-variable warning must produce a nonzero Lean exit status.
- The range-ledger invalidation mutation must fail elaboration.
- The executable release example must refuse the bad middle release and decline
  to apply the following release.
- All logical counterexamples in `Audit/` compile successfully as true statements
  refuting the invalid stronger claims.

A successful run writes `.lake/all-files-gate/receipt.json` and detailed logs.
The receipt records the commit, dirty status, source and gate-input SHA-256
hashes, dependency pins, compiler version, source coverage, declaration coverage,
standard-axiom allowlist, and control results. The gate fails if a source or its
configuration changes during the run. Only a clean run at an immutable commit
supports a statement that that exact commit passed.
