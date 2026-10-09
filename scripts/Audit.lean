import NLAlib
open Lean Elab Command

/-! Axiom audit. Every theorem in namespaces `NLAlib` and `TroppMatrixConcentration` may depend
only on `propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` for declared scaffolds.
Fails on any other axiom. Writes the list of declarations that depend on `sorryAx` to
`.lake/sorries.txt`; `scripts/check_atlas.py` checks that list against the atlas
(every sorried declaration must be a `scaffold` entry, and every `scaffold` entry must still
be sorried). Run with `lake env lean scripts/Audit.lean` after `lake build`. -/
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List Name := [`NLAlib, `TroppMatrixConcentration]
  let mut n : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut sorried : Array Name := #[]
  for (d, ci) in env.constants.map₁.toList do
    if roots.any (fun r => r.isPrefixOf d) && !d.isInternal then
      if let .thmInfo _ := ci then
        n := n + 1
        let axs ← collectAxioms d
        if axs.contains ``sorryAx then sorried := sorried.push d
        let extra := axs.filter (fun a => !allowed.contains a && a != ``sorryAx)
        if extra.size > 0 then bad := bad.push (d, extra)
  let sortedSorried := sorried.qsort (fun a b => a.toString < b.toString)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile ".lake/sorries.txt" (String.intercalate "\n" (sortedSorried.map toString).toList ++ "\n")
  logInfo m!"audited {n} theorems in {roots}; {sortedSorried.size} depend on sorry (scaffolds): {sortedSorried}"
  if bad.size = 0 then logInfo m!"OK: no axioms beyond propext / Classical.choice / Quot.sound (and sorryAx in scaffolds)"
  else
    for (d, ax) in bad do logError m!"{d} uses extra axioms {ax}"
