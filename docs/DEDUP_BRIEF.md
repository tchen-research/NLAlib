# Dedup and dependency review: brief for review agents

**Goal.** Find duplicated definitions and results, results Mathlib already has, and misplaced
helpers in one area of NLAlib, and write a concrete merge plan. This is a *review*: do not edit
any file under the repository. The coordinator merges the plans and runs the edit round.

## Inputs

- `atlas/declarations.json`: every public declaration (`name`, `kind`, `module`, `line`,
  `signature`, `doc`, `sorry`, `uses` = NLAlib definitions in the statement).
- Scratch listings (paths given in your task): `defs_all.txt` (every NLAlib definition with its
  module and first docstring sentence; use it to check your area's definitions against the
  *whole* library), `defs_<TopDir>.txt` (definitions of a top-level directory with signatures),
  `dup_signature_groups.txt` (theorems with identical statements up to bound-variable names,
  automatic scan), `def_name_collisions.txt` (definitions with near-identical names).
- `docs/STANDARDS.md` §1–§3: naming, file/layer rules, and the canonical vocabulary
  (`frobInner`, `frobSq`, `frobNorm`, `specNorm`, `HasOrthonormalCols`, `residual`, `pinvL`/`pinvR`,
  `singularValues`, `IsSVD`, `gaussianMatrix`, `IsSubspaceEmbedding`, `quadForm`, `krylovSpace`,
  `LoewnerLE`, `conditionNumber`, …). A second spelling of any of these is a defect.
- Mathlib source (pinned): `.lake/packages/mathlib/Mathlib/`. The library is built; a scratch file
  checks a statement against Mathlib with `exact?`:
  `cd /home/tyler/Documents/prove2me/lean && lake env lean <scratch>.lean` where the scratch file
  imports the relevant Mathlib modules (or `import Mathlib`) and contains
  `example … : <statement> := by exact?` (10–40 s per run; batch several examples in one file).

## What counts

1. **Duplicate definition**: two definitions of the same mathematical object, in any guise:
   different generality (`Fin n` vs `[Fintype ι]`, `ℝ` vs general field), a formula vs a
   characterisation, a copy inside a proof-specific namespace (`HansonWrightProof.*`,
   `SparseFock.*`, `Kaczmarz.*`), a structure field that duplicates a standalone definition.
2. **Duplicate result**: two theorems with the same mathematical content up to packaging
   (hypothesis order, bundled vs unbundled hypotheses, `Fin` vs `Fintype`, a trivially equivalent
   form). A theorem that is a special case of another with the same proof effort is **subsumed**
   (report it, lower priority). `≤` vs `<`, or one-sided vs two-sided, are not duplicates.
3. **In Mathlib**: a definition or theorem that Mathlib (pinned version) already provides, possibly
   under a different name or in slightly greater generality. Verify by reading the Mathlib
   declaration or by `exact?`; name the Mathlib declaration.
4. **Misplaced helper / Aux copy**: a general fact proved inside a topic file or a `private`/`Aux`
   namespace that belongs in `ForMathlib/…` or in the area that owns the concept (STANDARDS §2);
   a `ForMathlib` file that is really about NLAlib objects.
5. **Dependency smell**: a module importing a much higher layer or a heavy module for one lemma
   that belongs lower; a definition whose only purpose is to re-export another.

## For each finding

- `keep`: the canonical declaration (prefer: the more general; the one in the right layer/file;
  the name that follows STANDARDS §1 and the vocabulary list; the one with more users).
- `drop`: the declarations to delete (or, for a definition whose users are many, to turn into an
  `abbrev`/lemma bridging to the keeper as a first step).
- `uses`: for every dropped name, the number of files referencing it
  (`grep -rl "\bname\b" NLAlib | wc -l`), so the merger knows the blast radius.
- `difficulty`: `trivial` (delete, replace references), `adapt` (proof changes needed where the
  forms differ), `generalise` (keeper must first be generalised to cover the loser's uses).
- `action`: one or two sentences the merger can follow without re-deriving your analysis.

## Output

Write two files in the scratch directory given in your task:
- `review_<area>.md`: a short report (what you looked at, how many declarations, the findings
  grouped by kind, and anything you could not decide), and
- `review_<area>.json`: a list of findings
  `{"kind": "duplicate-def|duplicate-thm|in-mathlib|misplaced|dependency", "keep": name, "drop": [names], "modules": [modules touched], "uses": {name: count}, "difficulty": …, "action": …, "reason": …}`.
  Names are full (`NLAlib.…`) and modules are import paths. `keep` may be a Mathlib name.

Be concrete and conservative: a finding the merger cannot execute from your description is
worthless; a false "duplicate" costs a build. When two things look alike but differ in a
mathematically relevant way, say so in the report and leave them out of the JSON.
Cross-area findings are welcome (flag them `cross_area: true`); check your definitions against
`defs_all.txt`, and grep for your area's key lemmas elsewhere in the library.
