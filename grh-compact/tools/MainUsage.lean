import Main
open Lean Elab Command

def constClosure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut fuel := 100000000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        for m in ci.getUsedConstantsAsSet.toList do
          unless seen.contains m do todo := m :: todo
  return seen

/-- For every constant from a local module (Lib/New/Statements/Main), write
name, module, start line, end line, and 1/0 per root closure. -/
elab "#usage_dump " f:str roots:ident* : command => do
  let env ← getEnv
  let sets := roots.map (fun r => constClosure env [r.getId])
  let mut out : Array String := #[]
  out := out.push ("name\tmodule\tstart\tend\t" ++ String.intercalate "\t" (roots.toList.map (·.getId.toString)))
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some i =>
      let m := (env.header.moduleNames[i.toNat]!).toString
      if m.startsWith "Lib" || m.startsWith "New" || m == "Main" || m == "Statements" then
        let r ← findDeclarationRanges? n
        let (s, e) := match r with
          | some dr => (dr.range.pos.line, dr.range.endPos.line)
          | none => (0, 0)
        let flags := sets.toList.map (fun st => if st.contains n then "1" else "0")
        out := out.push (n.toString ++ "\t" ++ m ++ "\t" ++ toString s ++ "\t" ++ toString e ++ "\t" ++ String.intercalate "\t" flags)
  IO.FS.writeFile f.getString (String.intercalate "\n" out.toList)
  logInfo m!"rows {out.size}; closure sizes {sets.toList.map (·.size)}"
#usage_dump "usage.tsv" riemannHypothesis riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive New.LFunction_ne_zero_of_primeRemainder_le New.eventually_primeRemainder_le_rpow New.star_inequality New.eventually_exists_data New.Variety.PadicTest.le_ker_of_tiltNearZeros_le_ker New.exists_isRoot_cubic_constantCoeff_eq_zero
