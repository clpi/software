import Main
open Lean Elab Command

/-- Every constant reachable from `riemannHypothesis`: name, module index name, its used constants. -/
elab "#edge_dump_full " f:str : command => do
  let env ← getEnv
  let h ← IO.FS.Handle.mk f.getString .write
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[`riemannHypothesis]
  while h' : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let us := ci.getUsedConstantsAsSet.toList
      let m := match env.getModuleIdxFor? n with
        | some i => (env.header.moduleNames[i.toNat]!).toString
        | none => "?"
      h.putStrLn (n.toString ++ "\t" ++ m ++ "\t" ++ String.intercalate " " (us.map toString))
      for u in us do
        unless seen.contains u do todo := todo.push u
  h.flush
  logInfo m!"reachable {seen.size}"
#edge_dump_full "edges_full.tsv"
