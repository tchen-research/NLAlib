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
  0 `Matrix` · 1 `Concentration` · 2 `Gaussian` · 3 `Sketching` · 4 `LowRank`, `Estimation`,
  `Krylov` · 5 `Solvers`.
- `Basic.lean` in an area holds definitions, their `@[simp]` unfolding lemmas, and nothing
  else. Theorems go in topic files (`Estimation/Hutchinson.lean`, `Krylov/Polynomial.lean`).
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
  because Mathlib has no `MeasurableSpace (Matrix m n ℝ)`.
- Constants explicit, never `∃ C`. Degenerate cases match the source. Two-sided bounds are two
  theorems. General form first, corollaries after.
- Every hypothesis explicit; no `axiom`, no `native_decide`; `sorry` only in a named scaffold
  (docstring `SCAFFOLD: <atlas id>`, catalogued).

## 4. Docstrings

Every public declaration has one. First sentence: what it says in words. Then the source and
label (`HMT 2011, Thm 9.1`; `Tropp 2015, Thm 6.1.1`), the atlas id, and any deviation from the
printed statement (generalisation, different constant, side condition). For a ported proof, the
origin (`ported from Prove2me solution GaussianMatrix.full_rank_ae`).

## 5. Metadata

Every PR that adds or renames a result updates `atlas/atlas.json` (status, `formalizations` with
`decl` and `usage`, `depends_on`, and for new results `aliases`, `hypotheses`, `conclusion`,
`uses_defs`, `variants`) and regenerates `atlas/declarations.json`
(`lake env lean scripts/ExtractDecls.lean`). Renames ship a map in `docs/renames/<date>-<topic>.json`
(`{"old.name": "new.name"}`) so the atlas and any external reference can be updated mechanically.

## 6. Checks before a PR

```
lake build
lake env lean scripts/Audit.lean          # axioms; sorries must be catalogued scaffolds
lake env lean scripts/ExtractDecls.lean   # declaration index
python3 scripts/check_layers.py
python3 scripts/check_names.py            # naming and Basic.lean rules
python3 scripts/check_atlas.py
```
