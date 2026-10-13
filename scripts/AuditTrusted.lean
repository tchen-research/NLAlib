import NLAlib
open Lean Elab Command

/-! Check every library declaration reachable through the default import, including private
helpers, definitions and instances. No `sorryAx` or additional axioms are permitted. -/
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.map₁.toList do
    let inLibrary := match env.getModuleIdxFor? name with
      | some i => (`NLAlib).isPrefixOf env.header.moduleNames[i.toNat]!
      | none => false
    if inLibrary then
      count := count + 1
      let extra := (← collectAxioms name).filter (fun a => !allowed.contains a)
      unless extra.isEmpty do
        logError m!"Default import: {name} depends on forbidden axioms {extra}"
  logInfo m!"audited {count} declarations reachable through import NLAlib"
