import NLAlib
open Lean

/-! Minimal direct imports and Mathlib name collisions.

For every NLAlib module (except generated aggregators) computes the modules that its declarations
actually reference (constants in types and proof terms), then shrinks its import list to a minimal
subset of the current imports (plus the referenced modules when nothing else provides them) that
still reaches every referenced module through the reduced import graph; iterated to a fixpoint
across the library. Imports under `Mathlib.Tactic` are never dropped (they may be used only as
tactics). The result is a suggestion to be verified by `lake build`.

Also lists NLAlib declarations whose name without the `NLAlib.` prefix exists in Mathlib (or any
other imported library), with both types.

Run with `lake env lean scripts/ImportUsage.lean`; writes `atlas/import_usage.json`. -/

def jsonStr (s : String) : String := (Json.str s).compress

structure BitSet where
  data : ByteArray
  deriving Inhabited

namespace BitSet
def empty (n : Nat) : BitSet := ⟨ByteArray.mk (Array.replicate ((n + 7) / 8) 0)⟩
def get (b : BitSet) (i : Nat) : Bool :=
  (b.data.get! (i / 8)).toNat &&& (1 <<< (i % 8)) != 0
def set (b : BitSet) (i : Nat) : BitSet :=
  ⟨b.data.set! (i / 8) (UInt8.ofNat ((b.data.get! (i / 8)).toNat ||| (1 <<< (i % 8))))⟩
def union (a b : BitSet) : BitSet := Id.run do
  let mut d := a.data
  for i in [:d.size] do
    d := d.set! i (d.get! i ||| b.data.get! i)
  return ⟨d⟩
end BitSet

def isAggregatorModule (env : Environment) (modIdx : Nat) : Bool :=
  (env.header.moduleData[modIdx]!).constNames.isEmpty

#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let nMods := names.size
  let mut idxOf : Std.HashMap Name Nat := {}
  for i in [:nMods] do idxOf := idxOf.insert names[i]! i
  -- direct imports
  let mut imports : Array (Array Nat) := #[]
  for i in [:nMods] do
    let md := env.header.moduleData[i]!
    imports := imports.push (md.imports.filterMap fun imp => idxOf.get? imp.module)
  -- needed modules for NLAlib modules
  let isNLA (i : Nat) : Bool := (`NLAlib).isPrefixOf names[i]!
  let mut needed : Array (Array Nat) := Array.replicate nMods #[]
  let mut neededNames : Array (Array Name) := Array.replicate nMods #[]
  for i in [:nMods] do
    if isNLA i && !isAggregatorModule env i then
      let md := env.header.moduleData[i]!
      let mut s : Std.HashSet Nat := {}
      let mut ns : Array Name := #[]
      for ci in md.constants do
        for c in ci.getUsedConstantsAsSet.toList do
          match env.getModuleIdxFor? c with
          | some j =>
            let j := j.toNat
            if j != i && !s.contains j then
              s := s.insert j
              ns := ns.push names[j]!
          | none => pure ()
      needed := needed.set! i (s.toArray.qsort (· < ·))
      neededNames := neededNames.set! i ns
  let fixed (i : Nat) : Bool := !isNLA i || isAggregatorModule env i || needed[i]!.isEmpty
  let noDrop (j : Nat) : Bool := (`Mathlib.Tactic).isPrefixOf names[j]! || names[j]! == `Init
  -- iterate
  let mut cur := imports
  let mut changed := true
  let mut round := 0
  while changed && round < 12 do
    changed := false
    round := round + 1
    -- closures in index order (imports precede importers)
    let mut closure : Array BitSet := Array.replicate nMods (BitSet.empty nMods)
    for i in [:nMods] do
      let mut b := (BitSet.empty nMods).set i
      for j in cur[i]! do b := b.union closure[j]!
      closure := closure.set! i b
    for i in [:nMods] do
      if fixed i then continue
      let need := needed[i]!
      -- missing needed modules become direct imports
      let mut cand := cur[i]!
      for m in need do
        if !cand.any (fun j => (closure[j]!).get m) then
          cand := cand.push m
      -- greedy drop: an import is droppable if every needed module it reaches is reached by another kept import
      let mut keep : Array Nat := #[]
      for k in [:cand.size] do
        let j := cand[k]!
        if noDrop j then keep := keep.push j; continue
        let others := keep ++ cand.extract (k+1) cand.size
        let covered := need.all fun m => !(closure[j]!).get m || others.any fun o => (closure[o]!).get m
        if !covered then keep := keep.push j
      if keep != cur[i]! then
        changed := true
        cur := cur.set! i keep
  -- output
  let mut out : Array String := #[]
  for i in [:nMods] do
    if fixed i then continue
    let old := imports[i]!
    let new := cur[i]!
    let removed := old.filter (fun j => !new.contains j)
    let added := new.filter (fun j => !old.contains j)
    if removed.isEmpty && added.isEmpty then continue
    let nm (j : Nat) := jsonStr (toString names[j]!)
    out := out.push s!"{jsonStr (toString names[i]!)}: \{\"removed\": [{", ".intercalate (removed.map nm).toList}], \"added\": [{", ".intercalate (added.map nm).toList}], \"keep\": [{", ".intercalate (new.map nm).toList}]}"
  -- name collisions with other libraries
  let mut coll : Array String := #[]
  for (c, ci) in env.constants.map₁.toList do
    if !(`NLAlib).isPrefixOf c then continue
    if c.isInternal then continue
    let stripped := c.replacePrefix `NLAlib Name.anonymous
    if stripped.isAnonymous then continue
    match env.find? stripped with
    | some other =>
      match env.getModuleIdxFor? stripped, env.getModuleIdxFor? c with
      | some jo, some jc =>
        let fmtT ← Meta.MetaM.run' (Meta.ppExpr ci.type)
        let fmtO ← Meta.MetaM.run' (Meta.ppExpr other.type)
        coll := coll.push s!"\{\"nlalib\": {jsonStr (toString c)}, \"module\": {jsonStr (toString names[jc.toNat]!)}, \"other\": {jsonStr (toString stripped)}, \"other_module\": {jsonStr (toString names[jo.toNat]!)}, \"same_type\": {ci.type == other.type}, \"type\": {jsonStr (toString fmtT)}, \"other_type\": {jsonStr (toString fmtO)}}"
      | _, _ => pure ()
    | none => pure ()
  IO.FS.writeFile "atlas/import_usage.json" <|
    "{\"rounds\": " ++ toString round ++ ",\n\"imports\": {\n" ++ ",\n".intercalate out.toList ++ "\n},\n\"collisions\": [\n" ++ ",\n".intercalate coll.toList ++ "\n]}\n"
  IO.println s!"rounds {round}; modules with changed imports: {out.size}; name collisions: {coll.size}"
