import NLAlib
open Lean Elab Command

/-! Axiom audit. Every theorem in namespaces `NLAlib` and `TroppMatrixConcentration` may depend
only on `propext`, `Classical.choice`, `Quot.sound`. Run with `lake env lean scripts/Audit.lean`
after `lake build`. Fails (non-zero exit) on `sorryAx` or any other axiom. -/
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List Name := [`NLAlib, `TroppMatrixConcentration]
  let mut n : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (d, ci) in env.constants.map₁.toList do
    if roots.any (fun r => r.isPrefixOf d) && !d.isInternal then
      if let .thmInfo _ := ci then
        n := n + 1
        let axs ← collectAxioms d
        let extra := axs.filter (fun a => !allowed.contains a)
        if extra.size > 0 then bad := bad.push (d, extra)
  logInfo m!"audited {n} theorems in {roots}"
  if bad.size = 0 then logInfo m!"OK: only propext / Classical.choice / Quot.sound used"
  else
    for (d, ax) in bad do logError m!"{d} uses extra axioms {ax}"
