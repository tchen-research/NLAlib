import NLAlib.Experimental
open Lean Elab Command

/-! Axiom audit. Every declaration in namespace `NLAlib`, or declared in an `NLAlib` module (the
`_root_.Matrix.IsHermitian.*` dot-notation theorems, instances on `Matrix`), may depend
only on `propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` for declared scaffolds.
Fails on any other axiom. Writes the list of declarations that depend on `sorryAx` to
`.lake/sorries.txt`; `scripts/check_atlas.py` checks that list against the atlas
(every public sorried declaration must be recorded by the declaration index in an excluded
module, and every atlas `scaffold` entry must still be sorried). This audit covers the complete
development; `AuditTrusted.lean` separately forbids sorry in the default import.
Run with `lake env lean scripts/Audit.lean` after `lake build`. -/
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List Name := [`NLAlib]
  let mut n : Nat := 0
  let mut total : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut sorried : Array Name := #[]
  let mut directSorried : Array Name := #[]
  let inLib (d : Name) : Bool :=
    roots.any (fun r => r.isPrefixOf d) ||
      (match env.getModuleIdxFor? d with
        | some i => roots.any (fun r => r.isPrefixOf env.header.moduleNames[i.toNat]!)
        | none => false)
  for (d, ci) in env.constants.map₁.toList do
    if inLib d then
      total := total + 1
      let axs ← collectAxioms d
      if let some value := ci.value? (allowOpaque := true) then
        if value.getUsedConstants.contains ``sorryAx then
          directSorried := directSorried.push d
          let doc := (← findDocString? env d).getD ""
          unless (String.ofList (doc.toList.dropWhile Char.isWhitespace)).startsWith "SCAFFOLD:" do
            logError m!"{d} contains a direct sorry without a SCAFFOLD atlas tag"
      let extra := axs.filter (fun a => !allowed.contains a && a != ``sorryAx)
      if extra.size > 0 then bad := bad.push (d, extra)
      if !d.isInternal then
        if let .thmInfo _ := ci then
          n := n + 1
          if axs.contains ``sorryAx then sorried := sorried.push d
  let sortedSorried := sorried.qsort (fun a b => a.toString < b.toString)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile ".lake/sorries.txt" (String.intercalate "\n" (sortedSorried.map toString).toList ++ "\n")
  IO.FS.writeFile ".lake/direct-sorries.txt" (String.intercalate "\n"
    ((directSorried.qsort (fun a b => a.toString < b.toString)).map toString).toList ++ "\n")
  logInfo m!"audited {total} declarations ({n} public theorems) in {roots}; {sortedSorried.size} theorems depend on sorry: {sortedSorried}"
  if bad.size = 0 then logInfo m!"OK: no axioms beyond propext / Classical.choice / Quot.sound (and sorryAx in scaffolds)"
  else
    for (d, ax) in bad do logError m!"{d} uses extra axioms {ax}"
