# NLAlib standards

`docs/FOUNDATIONS_BRIEF.md` (2026-10-13) governs this repository until the port; where they
disagree, the brief wins.

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
  −1 `ForMathlib` · 0 `Matrix`, `Polynomial` · 1 `Probability`, `Krylov` · 2 `RandomMatrix` · 3 `Sketching` ·
  4 `LowRank`, `Estimation` · 5 `Solvers`. Each top-level directory is split into topic subdirectories
  (`Matrix/{Basic,Norms,Spectral,Subspaces,Factorizations,Perturbation,Inequalities,OperatorTheory,
  Functions,Structured,Calculus}`, `Probability/{Gaussian,Concentration,…}`, `RandomMatrix/{Gaussian,…}`,
  …; see `docs/REORG_PLAN.md`); content files live in those subdirectories and every `<Dir>.lean` is a
  generated aggregator, never edited by hand: after creating, moving or deleting a file run
  `python3 scripts/reorg.py --gen-aggregators`. Inside a leaf, `Basic.lean` holds
  definitions and their simp-level API only; a leaf's namesake file that carries theory as well is
  `Core.lean` (`Matrix/Norms/Core.lean`, `Matrix/Spectral/Core.lean`, …). `Krylov` is the deterministic theory (Krylov spaces,
  Lanczos, CG, Gauss quadrature); randomized Krylov guarantees live with their consumers in
  `LowRank` and `Estimation`. Krylov methods are defined by predicates or compressions, never by
  recurrences, and use two interfaces: "any orthonormal `Q` containing `K_q`" for approximant
  theorems and `LanczosDecomp` / `ArnoldiDecomp` (graded basis, `T := QᵀAQ`) for theorems about the
  structure of `T`. The conventions are `docs/KRYLOV_DEFINITIONS.md` §6 and §3.11–3.12. Direct algorithms
  (LU, Cholesky, QR, Hessenberg) follow `docs/ALGORITHM_CONVENTIONS.md`: factorization predicate,
  total recursion over `Fin n`, success predicate, realisation theorem; no finite precision yet.
- `NLAlib/ForMathlib/` holds general facts that are not about NLAlib's objects and are candidates
  for upstreaming (real inequalities, integrability of finite suprema, measure-preserving
  coordinate updates, `det ≠ 0` from full rank). Files are named after the Mathlib directory they
  would land in (`ForMathlib/Analysis/Real.lean`, `ForMathlib/MeasureTheory/Integral.lean`).
- The spectral core (`Matrix/Norms/{Frobenius,Core}`, `Matrix/Subspaces/Projections`,
  `Matrix/Basic/{Pseudoinverse,PenroseIdentities,MoorePenrose*,QuadForm}`,
  `Matrix/Spectral/{Core,SVD,CourantFischer,Weyl,EckartYoung}`, `Matrix/Inequalities/Mirsky`) is
  stated once, over `{𝕜 : Type*} [RCLike 𝕜]` and `{m n : Type*} [Fintype m] [Fintype n]` (plus
  `DecidableEq` where Mathlib needs it). There is no ℝ-only or ℂ-only copy of a core theorem: a
  `Complex*`/`Real*` twin is deleted and its users repointed. In layer 0, `Fin` appears only as a
  sorted position type: `rectDiag σ : Matrix (Fin p) (Fin q) 𝕜`, Mathlib's
  `IsHermitian.eigenvalues₀ : Fin (card n) → ℝ`, and the column index of SVD factors
  (`U : Matrix m (Fin p) 𝕜`, `V : Matrix n (Fin q) 𝕜`). Leaves still written over `Fin` or ℝ are
  frozen and generalised at port time (brief §0).
- Transpose twins are not written. A lemma is stated once with `ᴴ`; real users get the `ᵀ` form
  through Mathlib's `@[simp]` lemma `Matrix.conjTranspose_eq_transpose_of_trivial` (term-mode uses
  at ℝ elaborate by unfolding; a `rw` on a `ᵀ` goal needs
  `simp only [Matrix.conjTranspose_eq_transpose_of_trivial]` on the lemma or `rw [← …]` on the
  goal first). If the old real name did not mention `transpose`, the general lemma takes it
  (`frobInner_eq_trace`, `pinvL_mul`); otherwise the general lemma has the `conjTranspose` name and
  the `ᵀ` name is removed, with a `@[deprecated] alias` only if it is used outside the core, and
  recorded in `docs/renames/`. This replaces decision D1 of `docs/rclike/DESIGN.md` (real
  corollaries kept under their old names), which no longer applies. Lemmas that genuinely involve
  `ᵀ` over ℂ (`frobSq_transpose`, `specNorm_transpose`, `moorePenroseInverse_transpose`) are not
  twins and stay.
- Lemmas whose subject is a `Matrix.IsHermitian`, `Matrix.PosSemidef` or `Matrix.PosDef`
  hypothesis live in those namespaces, declared `theorem _root_.Matrix.IsHermitian.foo` inside
  `namespace NLAlib`, so dot notation works (`hA.eigenvalues₀_add_le`); `NLAlib.Matrix.IsHermitian.foo`
  is not found by `hA.foo`. Inside such a declaration, write NLAlib definitions whose name clashes
  with the namespace in full (`NLAlib.moorePenroseInverse`).
- The Loewner order is `A ≤ B` under `open scoped MatrixOrder` (`Matrix.le_iff`:
  `A ≤ B ↔ (B - A).PosSemidef`). Hypotheses are written with `≤`, never as `(B - A).PosSemidef`.
- `Basic.lean` in an area holds definitions, their `@[simp]` unfolding lemmas, and the
  definition's immediate API (for `gaussianMatrix`: the law of an entry, its first two moments,
  flattening, measurability, the `IsGaussian` instance), and nothing else. Theorems go in topic
  files (`Estimation/Hutchinson.lean`, `Krylov/Polynomial.lean`). `scripts/name_exemptions.txt`
  lists the API lemmas allowed in a `Basic.lean`.
- Helpers go where they belong, not where they were first needed: a Frobenius inequality goes in
  `Matrix/Norms/Frobenius.lean`, a projector identity in `Matrix/Subspaces/Projections.lean`, a
  measurability fact about matrices in `Matrix/Structured/Measurable.lean`. A local `Aux` namespace with copies of library
  lemmas is a defect, not a convention.
- `private` is for proof-local scaffolding only. Anything a second file could want is public,
  named by §1, and documented.
- Imports are the specific Mathlib files needed (`import Mathlib` only in scratch files).
  Dependency tools: `lake env lean scripts/ImportUsage.lean` computes, for every module, the
  imports its declarations actually use and a minimal import list (and lists NLAlib names that
  collide with Mathlib), written to `atlas/import_usage.json`; `python3 scripts/apply_imports.py`
  applies those suggestions (`--revert M …` restores a module's import block). Verify with
  `lake build` of the touched modules and their dependants.

## 3. Statements

- Index types: `[Fintype m] [Fintype n]` everywhere in the Matrix layer, and wherever a statement
  does not touch a Gaussian law (the sorted positions of §2 are the only `Fin` in layer 0).
  `Fin n` only where a Gaussian law needs the product measure (`gaussianMatrix p m` lives on
  `Fin p → Fin m → ℝ`); F2 revisits this (`gaussianMatrix m n` on `Matrix m n ℝ`, planned,
  `docs/FOUNDATIONS_BRIEF.md` §2). A theorem stated over `Fin` because a dependency was, is a
  defect to fix at the dependency.
- Vocabulary (over `𝕜` unless marked ℝ): `frobInner A B` (the real part of the Frobenius pairing,
  `RCLike.re (∑ i, ∑ j, star (A i j) * B i j)`; the `𝕜`-valued pairing is `(Aᴴ * B).trace` and has
  no name), `frobSq`, `frobNorm` (bridge `frobNorm_eq_norm` to Mathlib's Frobenius norm under
  `open scoped Matrix.Norms.Frobenius`); `specNorm A` (`= ‖A‖` under the L2 operator norm, bridge
  `specNorm_eq_norm`; it needs `[DecidableEq n]` on the column index only, no `[DecidableEq m]`);
  core and merged files state norms with `specNorm`/`frobNorm`, `‖A‖` under
  `open scoped Matrix.Norms.L2Operator` is written directly only in the CFC and Probability files;
  `HasOrthonormalCols Q := Qᴴ * Q = 1` (take the hypothesis in this form; at ℝ a `Qᵀ * Q = 1` term
  elaborates against it, and a `Qᵀ * Q` goal is rewritten with `hQ.conjTranspose_mul_self` after
  `rw [← Matrix.conjTranspose_eq_transpose_of_trivial]`); `residual Q A = A - Q * (Qᴴ * A)`;
  `quadForm A z := star z ⬝ᵥ (A *ᵥ z)` (`𝕜`-valued, Mathlib's `PosSemidef` form; real consumers take
  `RCLike.re`, and over ℂ `0 ≤ quadForm A z` needs `open scoped ComplexOrder`) and
  `rayleighQuotient A x` (real-valued); two pseudoinverses: `moorePenroseInverse A`
  (Basic/MoorePenrose) is the general Moore–Penrose inverse, defined for every matrix including
  rank-deficient and empty ones, and is the default in statements; `pinvL A = (AᴴA)⁻¹Aᴴ` and
  `pinvR A = Aᴴ(AAᴴ)⁻¹` (Basic/Pseudoinverse) are the full-rank formulas, used with an explicit
  `IsUnit (Aᴴ * A)` / `IsUnit (A * Aᴴ)` hypothesis only when a proof computes with the formula
  (sketching, range finders); the bridges are `moorePenroseInverse_eq_pinvL`,
  `moorePenroseInverse_eq_pinvR`; `singularValues A : ℕ → ℝ` (over any `[Fintype m] [Fintype n]`,
  zero-padded, antitone; never spell it `(Matrix.toEuclideanLin A).singularValues`, the bridge to
  Mathlib's `LinearMap.singularValues` is `singularValues_eq_linearMap`, by `rfl`); `IsSVD A U V`
  with `U : Matrix m (Fin p) 𝕜`, `V : Matrix n (Fin q) 𝕜` (fields `conjTranspose_mul_left/right`,
  `eq : A = U * rectDiag (singularValues A) * Vᴴ`, `mul_conjTranspose_left/right`), obtained by
  `obtain ⟨U, V, hA⟩ := exists_isSVD A`, whose auto-params set `p = card m`, `q = card n` (square
  `Fin a` factors at `Fin a` indices; decision E′, `docs/rclike/F1b-alpha.md`); the smallest
  eigenvalue of a Hermitian `A` is `hA.eigenvalues₀ ⟨Fintype.card n - 1, _⟩` (Rayleigh form
  `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`), with no `lamMin`; the Loewner order `≤` (§2);
  `gaussianMatrix p m` with `Matrix.of` as the matrix view and `linForm c G` for its linear forms
  (ℝ); `IsSubspaceEmbedding S U ε` (ℝ); `krylovSpace A b q` (over any field, as are
  `blockKrylovSpace` and `subspaceIterate`; the Krylov methods stay real); the matrix function
  `cfc f A` (Mathlib) with `matrixExp`, `matrixLog`, `traceExp`. Do not introduce a second spelling
  of any of these.
- Probability: an abstract space `{Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]`,
  random matrices as functions, laws as `μ.map X = …`, expectations as Bochner integrals.
  Prefer statements without integrability hypotheses (prove the `lintegral` form, then convert);
  measurability of matrix-valued maps is stated entrywise (`∀ i j, Measurable fun x => T x i j`)
  because Mathlib has no `MeasurableSpace (Matrix m n ℝ)`. (One deliberate exception: the matrix
  concentration files use a global Borel instance on `Matrix m n ℂ`, `matrixMeasurableSpace` /
  `matrixBorelSpace`, inherited from the Tropp port and documented in
  `Probability/Concentration/Basic/MatrixStatistics.lean`.) Planned, `docs/FOUNDATIONS_BRIEF.md`
  §2 (F2): both are replaced by a global `Matrix.instMeasurableSpace` / `Matrix.instBorelSpace` in
  `ForMathlib/MeasureTheory/Matrix.lean`, so a random matrix is `X : Ω → Matrix m n 𝕜`; laws are
  stated with Mathlib's `HasLaw X (gaussianMatrix m n) μ` instead of `μ.map X = …`; tails are
  `μ.real s ≤ …`.
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

A foundation-change PR (`docs/FOUNDATIONS_BRIEF.md` §1–2) also pastes these greps into its
description. F1 (each should print nothing):

```
CORE=$(ls NLAlib/Matrix/Norms/{Frobenius,Core}.lean NLAlib/Matrix/Subspaces/Projections.lean \
  NLAlib/Matrix/Basic/{Pseudoinverse,PenroseIdentities,QuadForm}.lean NLAlib/Matrix/Basic/MoorePenrose*.lean \
  NLAlib/Matrix/Spectral/{Core,SVD,CourantFischer,Weyl,EckartYoung}.lean NLAlib/Matrix/Inequalities/Mirsky.lean)
grep -n "Matrix (Fin" $CORE | grep -v "rectDiag\|Matrix (Fin p) (Fin q)"   # sorted positions exempt
grep -rn "_fin\b" NLAlib/Matrix | grep -v "card_fin"                        # Mathlib names exempt
for f in ComplexVariationalPrinciple ComplexRectangularSVD ComplexBestRankApproximation \
  ComplexGramTruncation ComplexEckartYoung ComplexVolumeSpectrum ComplexSingularTransport \
  RealComplexNorm ComplexFrobenius RealComplexCFC ComplexEmbedding FiniteIndexTransport; do
  find NLAlib/Matrix -name "$f.lean"; done                                  # deleted twins
```

The brief's directory-wide `grep -rl "Matrix (Fin" NLAlib/Matrix/{Spectral,Norms,Basic}` also hits
frozen non-core leaves; only the core list above is the acceptance criterion. Exempt are `rectDiag`
and its ascriptions `Matrix (Fin p) (Fin q) 𝕜`, the `Fin p` column index of SVD factors, docstrings,
and Mathlib names such as `Fintype.card_fin`. `grep -rl "ℂ" NLAlib/Matrix/Spectral` may list no file
that has an ℝ sibling among the core (`ComplexQZ`/`RealQZ` are outside F1). F2 (each should print
nothing, once F2 has landed):

```
grep -rn "Matrix.of.symm" NLAlib | grep -v "ForMathlib/MeasureTheory/Matrix.lean"
grep -rn "μ.map .* = gaussianMatrix\|\.map .* = gaussianMatrix" NLAlib
grep -rn "instance.*MeasurableSpace\|instance.*BorelSpace" NLAlib | grep -v "ForMathlib/MeasureTheory/Matrix.lean"
grep -rn "_of_map_eq" NLAlib
```
