# NLAlib standards

The rules every file in `NLAlib/` follows. CONTRIBUTING.md says how to work; this says what the
result must look like. `scripts/check_names.py` enforces the mechanical parts.

## 1. Names (Mathlib conventions)

Reference: https://leanprover-community.github.io/contribute/naming.html.

| Kind | Case | Examples |
|---|---|---|
| theorem, lemma | `snake_case` | `frobSq_nonneg`, `pinvL_mul`, `specNorm_le_frobNorm` |
| def returning data | `lowerCamelCase` | `frobSq`, `singularValues`, `krylovSpace`, `sketchedCore` |
| structure, class, inductive, Prop-valued predicate | `UpperCamelCase` | `IsSVD`, `HasOrthonormalCols`, `IsSubspaceEmbedding` |
| namespace, file, directory | `UpperCamelCase` | `NLAlib.Kaczmarz`, `Matrix/Pseudoinverse.lean` |

A theorem name spells its conclusion left to right, joining the head symbols with `_`:
`frobSq_mul_le_specNorm_sq_mul_frobSq` is `frobSq (A * B) ≤ specNorm A ^ 2 * frobSq B`.
Standard pieces: `_eq`, `_le`, `_lt`, `_iff`, `_ne_zero`, `_pos`, `_nonneg`, `_comm`, `_assoc`,
`_left`, `_right`, `_apply`, `_def`, `exists_`, `_of_<hypothesis>`. Measure theory prefixes name
the left-hand side: `integral_`, `lintegral_`, `ae_`, `measurable_`, `integrable_`, `variance_`.
Hypotheses are `h`-prefixed (`hA`, `hQ`, `hkt`).

Lemmas about a structure live in its namespace for dot notation: `IsSVD.mul_right`,
`IsSubspaceEmbedding.mono`. A small family of related definitions may share a namespace
(`Kaczmarz.step`, `Kaczmarz.expErr`).

Never name a declaration after its source. `rangeFinder_frobSq_le`, `hmt_second_frob`,
`ch5_matrix_chernoff`, `tail_bound` are wrong; `frobSq_residual_le_of_range_subset`,
`matrix_chernoff`, `sq_singularValue_le_avg_tail` are right. The source goes in the docstring.

Named constants and tail expressions are definitions, named for what they are:
`bernsteinTail d v L t`, `chernoffUpperTail`.

Before the `v0.1` tag renames are direct. From `v0.1` on, a renamed public declaration keeps a
`@[deprecated (since := "YYYY-MM-DD")] alias old := new` for one release.

## 2. Files and layers

- One concept per file, under about 500 lines, `UpperCamelCase.lean`, with a module docstring
  `/-! # Title … -/` that says what the file provides and names the atlas ids it realises.
- Layers (a module imports only its own layer and lower; `scripts/check_layers.py`):
  −1 `ForMathlib` · 0 `Matrix`, `Polynomial` · 1 `Concentration`, `Krylov` · 2 `Gaussian` · 3 `Sketching` ·
  4 `LowRank`, `Estimation` · 5 `Solvers`. `Krylov` is the deterministic theory (Krylov spaces,
  Lanczos, CG, Gauss quadrature); randomized Krylov guarantees live with their consumers in
  `LowRank` and `Estimation`. Krylov methods are defined by predicates or compressions, never by
  recurrences, and use two interfaces: "any orthonormal `Q` containing `K_q`" for approximant
  theorems and `LanczosDecomp` / `ArnoldiDecomp` (graded basis, `T := QᵀAQ`) for theorems about the
  structure of `T`. The conventions are `docs/KRYLOV_DEFINITIONS.md` §6 and §3.11–3.12.
- `NLAlib/ForMathlib/` holds general facts that are not about NLAlib's objects and are candidates
  for upstreaming (real inequalities, integrability of finite suprema, measure-preserving
  coordinate updates, `det ≠ 0` from full rank). Files are named after the Mathlib directory they
  would land in (`ForMathlib/Analysis/Real.lean`, `ForMathlib/MeasureTheory/Integral.lean`).
- `Basic.lean` in an area holds definitions, their `@[simp]` unfolding lemmas, and the
  definition's immediate API (for `gaussianMatrix`: the law of an entry, its first two moments,
  flattening, measurability, the `IsGaussian` instance), and nothing else. Theorems go in topic
  files (`Estimation/Hutchinson.lean`, `Krylov/Polynomial.lean`). `scripts/name_exemptions.txt`
  lists the API lemmas allowed in a `Basic.lean`.
- Helpers go where they belong, not where they were first needed: a Frobenius inequality goes in
  `Matrix/Norms.lean`, a projector identity in `Matrix/Projections.lean`, a measurability fact
  about matrices in `Matrix/Measurable.lean`. A local `Aux` namespace with copies of library
  lemmas is a defect, not a convention.
- `private` is for proof-local scaffolding only. Anything a second file could want is public,
  named by §1, and documented.
- Imports are the specific Mathlib files needed (`import Mathlib` only in scratch files).

## 3. Statements

- Index types: `[Fintype ι]` whenever the statement does not touch a Gaussian law; `Fin n`
  when it does (the product measure lives on `Fin p → Fin m → ℝ`). A theorem stated over `Fin`
  because a dependency was, is a defect to fix at the dependency.
- Vocabulary: `frobInner`, `frobSq`, `frobNorm`, `specNorm` (bridge `specNorm_eq_norm`);
  `HasOrthonormalCols Q` for `Qᵀ * Q = 1` (take the hypothesis in this form, it unfolds);
  `residual Q A`; `pinvL`, `pinvR` with explicit `IsUnit` side conditions until the general
  pseudoinverse exists; `singularValues A : ℕ → ℝ` and `IsSVD A U V`; `gaussianMatrix p m` with
  `Matrix.of` as the matrix view; `IsSubspaceEmbedding S U ε`; `quadForm A z`;
  `krylovSpace A b q`. Do not introduce a second spelling of any of these.
- Probability: an abstract space `{Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]`,
  random matrices as functions, laws as `μ.map X = …`, expectations as Bochner integrals.
  Prefer statements without integrability hypotheses (prove the `lintegral` form, then convert);
  measurability of matrix-valued maps is stated entrywise (`∀ i j, Measurable fun x => T x i j`)
  because Mathlib has no `MeasurableSpace (Matrix m n ℝ)`. (One deliberate exception: the matrix
  concentration files declare a global Borel instance on `Matrix m n ℂ`, inherited from the Tropp
  port and documented in `Concentration/Matrix/Defs/Probability.lean`.)
- Constants explicit, never `∃ C`. Degenerate cases match the source. Two-sided bounds are two
  theorems. General form first, corollaries after.
- Every hypothesis explicit; no `axiom`, no `native_decide`; `sorry` only in a named scaffold
  (docstring `SCAFFOLD: <atlas id>`, catalogued).
- Scaffolding well-known theorems is encouraged, not merely tolerated: a confidently stated
  textbook or published result may enter as a scaffold (or as an explicit hypothesis, atlas
  `assumed`) so that the tree below it can be built now. The statement must be checked with the
  same care as a proved one, since a wrong assumption propagates to every consumer.

## 4. Docstrings

Every public declaration has one. First sentence: what it says in words. Then the source and
label (`HMT 2011, Thm 9.1`; `Tropp 2015, Thm 6.1.1`) and any deviation from the printed statement
(generalisation, different constant, side condition). For a ported proof, the origin (`ported from
Prove2me solution GaussianMatrix.full_rank_ae`). A declaration that is the formal statement of an
atlas result ends with the tag line `atlas: <id>` (comma-separated ids if several; `<id> (partial)`
when the declaration covers only part of the statement); a helper names the id in prose only. The
tag is machine-read: it is what links the declaration to the atlas.

## 5. Metadata

The Lean side of `atlas/atlas.json` is generated: `scripts/ExtractDecls.lean` indexes every public
declaration (signature, docstring, `sorry` dependence, `atlas:` tags, NLAlib definitions in the
statement) and `scripts/sync_atlas.py` rewrites each result's `formalizations`, `status` and
`uses_defs` from that index. A PR that adds a result writes the human side by hand (title,
`informal`, `hypotheses`, `conclusion`, `sources`, `depends_on`, `aliases`, `variants`), tags the
declarations, and runs the two scripts. Statements that exist in Mathlib are not atlas results; a
consumer cites them under `mathlib_prereqs`. Renames ship a map in `docs/renames/<date>-<topic>.json`
(`{"old.name": "new.name"}`) so the atlas and any external reference can be updated mechanically.

## 6. Checks before a PR

```
lake build
lake env lean scripts/Audit.lean          # axioms; sorries must be catalogued scaffolds
lake env lean scripts/ExtractDecls.lean   # declaration index (+ atlas/external.json)
python3 scripts/sync_atlas.py             # Lean side of atlas.json from the `atlas:` tags
python3 scripts/check_layers.py
python3 scripts/check_names.py            # naming and Basic.lean rules
python3 scripts/check_atlas.py
```
