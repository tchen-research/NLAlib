import NLAlib
open Lean Elab Command Meta

/-! Declaration index for search, for prover agents and for the atlas.

Writes `atlas/declarations.json`: every public declaration in namespace `NLAlib` with its kind,
module (import path), pretty-printed signature, docstring, source line, whether it depends on
`sorry`, the atlas ids its docstring tags (`atlas: <id>, <id> (partial)` lines, or a leading
`SCAFFOLD: <id>`; partial ids also under `atlas_partial`), and the NLAlib definitions that occur
in its statement (`uses`).

Also writes `atlas/external.json`: the same record for every declaration from another library
(Mathlib, …) that `atlas/atlas.json` cites under `formalizations` or `mathlib_prereqs`, so the
atlas can show its Lean statement.

Generated; do not edit. Run with `lake env lean scripts/ExtractDecls.lean` after `lake build`. -/

/-- Auto-generated name components: `_x`, `match_1`, `proof_2`, `eq_1`. -/
def isAutoComponent (s : String) : Bool :=
  s.startsWith "_" ||
  ["match_", "proof_", "eq_"].any fun p =>
    s.startsWith p && !(s.drop p.length).isEmpty &&
      (s.drop p.length).all (fun c => c.isDigit || c == '_')

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- The leading `[A-Za-z0-9-]*` of a string after dropping `k` characters and whitespace. -/
def idAfter (s : String) (k : Nat) : String :=
  String.ofList (((s.toList.drop k).dropWhile Char.isWhitespace).takeWhile
    fun c => c.isAlphanum || c == '-')

/-- Atlas ids tagged in a docstring: every `atlas: a, b (partial)` line, plus the id of a leading
`SCAFFOLD: <id>`. Returns `(ids, partial ids)`: an id followed by `(partial)` formalizes only part
of the result (it is listed, but does not make the result proved). -/
def atlasTags (doc : String) : Array String × Array String := Id.run do
  let mut out : Array String := #[]
  let mut part : Array String := #[]
  let t := String.ofList (doc.toList.dropWhile Char.isWhitespace)
  if t.startsWith "SCAFFOLD:" then
    let id := idAfter t "SCAFFOLD:".length
    if id.length > 0 then out := out.push id
  for line in doc.splitOn "\n" do
    let l := String.ofList (line.toList.dropWhile Char.isWhitespace)
    if l.startsWith "atlas:" then
      for piece in (String.ofList (l.toList.drop "atlas:".length)).splitOn "," do
        let id := idAfter piece 0
        if id.length > 0 && !out.contains id then
          out := out.push id
          if (piece.splitOn "(partial)").length > 1 then part := part.push id
  return (out, part)

def isPublicName (roots : List Name) (n : Name) : Bool :=
  roots.any (fun r => r.isPrefixOf n) && !n.isInternal && !isPrivateName n
    && !(n.toString.splitOn ".").any isAutoComponent

def record (env : Environment) (n : Name) (ci : ConstantInfo) (isDef : Name → Bool)
    : CommandElabM Json := do
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
  let uses := (ci.type.getUsedConstants.filter fun c => c != n && isDef c)
    |>.qsort (fun a b => a.toString < b.toString) |>.map (fun c => Json.str c.toString)
  pure <| Json.mkObj [
    ("name", toString n), ("kind", if isInst then "instance" else kindOf ci),
    ("module", modName), ("line", line), ("signature", sig), ("doc", doc),
    ("sorry", sorried), ("atlas", Json.arr ((atlasTags doc).1 |>.map Json.str)),
    ("atlas_partial", Json.arr ((atlasTags doc).2 |>.map Json.str)),
    ("uses", Json.arr uses)]

run_cmd do
  let env ← getEnv
  let roots : List Name := [`NLAlib]
  let names := env.constants.map₁.toList.filterMap fun (n, ci) =>
    if isPublicName roots n then some (n, ci) else none
  let names := names.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  -- NLAlib definitions (not theorems, not instances, not recursors): what `uses` may contain
  let isDef : Name → Bool := fun c =>
    isPublicName roots c && match env.find? c with
      | some (.defnInfo _) | some (.inductInfo _) | some (.opaqueInfo _)
      | some (.axiomInfo _) => true
      | _ => false
  let mut out : Array Json := #[]
  for (n, ci) in names do
    if kindOf ci == "recursor" then continue
    out := out.push (← record env n ci isDef)
  IO.FS.createDirAll "atlas"
  IO.FS.writeFile "atlas/declarations.json" ((Json.arr out).pretty 1 ++ "\n")
  logInfo m!"wrote {out.size} declarations to atlas/declarations.json"
  -- external declarations cited by the atlas
  let atlas ← IO.FS.readFile "atlas/atlas.json"
  let mut ext : Array Json := #[]
  let mut missing : Array String := #[]
  match Json.parse atlas with
  | .error e => logError m!"atlas/atlas.json: {e}"
  | .ok j =>
    let results := (j.getObjVal? "results" >>= Json.getArr?).toOption.getD #[]
    let mut seen : Array String := #[]
    for r in results do
      let fs := (r.getObjVal? "formalizations" >>= Json.getArr?).toOption.getD #[]
      let ms := (r.getObjVal? "mathlib_prereqs" >>= Json.getArr?).toOption.getD #[]
      for f in fs ++ ms do
        -- `mathlib_prereqs` entries carry no `library`; they are Mathlib by definition
        let lib := (f.getObjValAs? String "library").toOption.getD "mathlib"
        let decl := (f.getObjValAs? String "decl").toOption.getD ""
        if lib == "nlalib" || decl == "" || seen.contains decl then continue
        seen := seen.push decl
        let n := decl.toName
        match env.find? n with
        | some ci =>
          let rec_ ← record env n ci isDef
          ext := ext.push (rec_.setObjVal! "library" (Json.str lib))
        | none => missing := missing.push s!"{lib}: {decl}"
  IO.FS.writeFile "atlas/external.json" ((Json.arr ext).pretty 1 ++ "\n")
  logInfo m!"wrote {ext.size} external declarations to atlas/external.json"
  if missing.size > 0 then
    logInfo m!"not found in the imported environment (left for check_atlas):\n{missing}"
