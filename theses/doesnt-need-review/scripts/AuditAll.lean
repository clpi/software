import Lean

open Lean Elab Command

/-- Audit every kernel-safe declaration introduced in a named module, including private
    declarations and generated auxiliaries. Imported dependencies are followed by
    the kernel's axiom collector. This is a policy check, not a theorem about the
    Lean implementation or arbitrary metaprogram execution. -/
elab "audit_module_declarations" target:ident : command => do
  let env ← getEnv
  let targetName := target.getId
  let some targetIndex := env.getModuleIdx? targetName |
    throwError "module was not imported: {targetName}"
  let mut names : Array Name := #[]
  let mut implementationAuxiliaries := 0
  for (name, info) in env.checked.get.constants do
    if env.getModuleIdxFor? name == some targetIndex then
      if info.isUnsafe then
        implementationAuxiliaries := implementationAuxiliaries + 1
      else
        names := names.push name
  names := names.qsort (fun a b => a.toString < b.toString)
  for name in names do
    let some _ := env.checked.get.find? name | throwError "missing declaration {name}"
    let axioms ← Lean.collectAxioms name
    for dependency in axioms do
      unless dependency == ``propext || dependency == ``Classical.choice ||
          dependency == ``Quot.sound do
        throwError "unapproved kernel axiom {dependency} in {name}"
  liftIO <| IO.println s!"ALL_DECLARATIONS_AUDITED {names.size} IMPLEMENTATION_AUXILIARIES {implementationAuxiliaries}"
