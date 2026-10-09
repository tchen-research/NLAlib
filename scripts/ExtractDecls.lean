import NLAlib
open Lean Elab Command Meta

/-! Declaration index for search and for prover agents.

Writes `atlas/declarations.json`: every public declaration in namespace `NLAlib` with its kind, module (import path), pretty-printed signature,
docstring, source file and line, and whether it depends on `sorry`. Generated; do not edit.
Run with `lake env lean scripts/ExtractDecls.lean` after `lake build`. -/

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

run_cmd do
  let env ← getEnv
  let roots : List Name := [`NLAlib]
  let mut out : Array Json := #[]
  let names := env.constants.map₁.toList.filterMap fun (n, ci) =>
    if roots.any (fun r => r.isPrefixOf n) && !n.isInternal && !isPrivateName n
      && !(n.toString.splitOn ".").any (fun s => s.startsWith "_") then some (n, ci) else none
  let names := names.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (n, ci) in names do
    -- skip auto-generated structure projections/recursors noise but keep structure fields
    if (kindOf ci == "recursor") then continue
    let modName := match env.getModuleIdxFor? n with
      | some idx => (env.header.moduleNames[idx.toNat]?).map toString |>.getD ""
      | none => ""
    let doc := (← findDocString? env n).getD ""
    let sig ← liftTermElabM do
      let f ← PrettyPrinter.ppSignature n
      pure f.fmt.pretty
    let ranges ← findDeclarationRanges? n
    let line := match ranges with | some r => r.range.pos.line | none => 0
    let axs ← collectAxioms n
    let sorried := axs.contains ``sorryAx
    let isInst ← liftCoreM (isInstance n)
    out := out.push <| Json.mkObj [
      ("name", toString n), ("kind", if isInst then "instance" else kindOf ci),
      ("module", modName), ("line", line), ("signature", sig), ("doc", doc),
      ("sorry", sorried)]
  let json := Json.arr out
  IO.FS.createDirAll "atlas"
  IO.FS.writeFile "atlas/declarations.json" (json.pretty 1 ++ "\n")
  logInfo m!"wrote {out.size} declarations to atlas/declarations.json"
