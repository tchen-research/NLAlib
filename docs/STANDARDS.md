# NLAlib standards

This is the authoritative, current policy for the library. Older briefs, including
`docs/FOUNDATIONS_BRIEF.md` and `docs/F4_CONSISTENCY_BRIEF.md`, record decisions and migration
history; follow this file where they conflict. `CONTRIBUTING.md` describes the workflow. Scripts
may check mechanical conventions, but a lint rule does not override the mathematical requirements
below.

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

Extend the owning Mathlib namespace for lemmas about Mathlib objects when this enables ordinary
dot notation. Put declarations for NLAlib-specific objects in their domain namespace. `NLAlib` is
not required as a wrapper namespace for every declaration.

Never name a declaration after its source. `rangeFinder_frobSq_le`, `hmt_second_frob`,
`ch5_matrix_chernoff`, `tail_bound` are wrong; `frobSq_residual_le_of_range_subset`,
`matrix_chernoff`, `sq_singularValue_le_avg_tail` are right. The source goes in the docstring.

Named constants and tail expressions are definitions, named for what they are:
`bernsteinTail d v L t`, `chernoffUpperTail`.

Before the `v0.1` tag, public renames are direct and call sites are updated in the same change.
From `v0.1` on, retain a deprecated alias for one release before removal.

## 2. Files and layers

- One concept per file, under about 500 lines, `UpperCamelCase.lean`, with a module docstring
  `/-! # Title … -/` that says what the file provides and names the atlas ids it realises.
- Layers (a module imports only its own layer and lower; `scripts/check_layers.py`):
  −1 `ForMathlib` · 0 `Matrix`, `Polynomial` · 1 `Probability`, `Krylov` · 2 `RandomMatrix` · 3 `Sketching` ·
  4 `LowRank`, `Estimation` · 5 `Solvers`. Each top-level directory is split into topic subdirectories
  (`Matrix/{Basic,Norms,Spectral,Subspaces,Factorizations,Perturbation,Inequalities,OperatorTheory,
  Functions,Structured,Calculus}`, `Probability/{Gaussian,Concentration,…}`, `RandomMatrix/{Gaussian,…}`,
  …); content files live in those subdirectories and every `<Dir>.lean` is a
  generated aggregator, never edited by hand: after creating, moving or deleting a file run
  `python3 scripts/reorg.py --gen-aggregators`. Inside a leaf, `Basic.lean` holds
  definitions and foundational API; further theory can live in topic files such as
  `Core.lean` (`Matrix/Norms/Core.lean`, `Matrix/Spectral/Core.lean`, …). `Krylov` is the deterministic theory (Krylov spaces,
  Lanczos, CG, Gauss quadrature); randomized Krylov guarantees live with their consumers in
  `LowRank` and `Estimation`. Krylov APIs may state specifications, recurrences, or executable
  processes. When a theorem is presented as a guarantee of a named algorithm, provide a realization
  bridge showing that the algorithm meets the specification and state the guarantee's actual scope.
  Direct algorithms
  (LU, Cholesky, QR, Hessenberg) follow `docs/ALGORITHM_CONVENTIONS.md`: factorization predicate,
  total recursion over `Fin n`, success predicate, realisation theorem; no finite precision yet.
- `NLAlib/ForMathlib/` holds general facts that are not about NLAlib's objects and are candidates
  for upstreaming (real inequalities, integrability of finite suprema, measure-preserving
  coordinate updates, `det ≠ 0` from full rank). Files are named after the Mathlib directory they
  would land in (`ForMathlib/Analysis/Real.lean`, `ForMathlib/MeasureTheory/Integral.lean`).
- The spectral core (`Matrix/Norms/{Frobenius,Core}`, `Matrix/Subspaces/Projections`,
  `Matrix/Basic/{Pseudoinverse,PenroseIdentities,MoorePenrose*,QuadForm}`,
  `Matrix/Spectral/{Core,SVD,CourantFischer,Weyl,EckartYoung}`, `Matrix/Inequalities/Mirsky`) is
  stated over `{𝕜 : Type*} [RCLike 𝕜]` and finite index types when the mathematics and available
  API naturally support that generality (plus `DecidableEq` where Mathlib needs it). Prefer a shared
  generic theorem over duplicated real and complex core statements, while allowing useful specialized
  corollaries and algorithmic representations. `Fin` is appropriate for algorithms and constructions
  that use its order, recursion, or dimension structure, as well as sorted positions such as
  `rectDiag σ : Matrix (Fin p) (Fin q) 𝕜`, Mathlib's
  `IsHermitian.eigenvalues₀ : Fin (card n) → ℝ`, and the column index of SVD factors
  (`U : Matrix m (Fin p) 𝕜`, `V : Matrix n (Fin q) 𝕜`). Generalize when doing so improves reuse and
  reflects the mathematics; do not impose generality solely to satisfy an index-type rule.
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
- `Basic.lean` in an area holds definitions and foundational API. It may also contain substantive
  theorems when they are foundational to the area's objects or fit naturally with the API; place
  other developments in topic files. No theorem is restricted by a filename or naming heuristic.
- Helpers go where they belong, not where they were first needed: a Frobenius inequality goes in
  `Matrix/Norms/Frobenius.lean`, a projector identity in `Matrix/Subspaces/Projections.lean`, a
  measurability fact about matrices in `Matrix/Structured/Measurable.lean`. A local `Aux` namespace with copies of library
  lemmas is a defect, not a convention.
- Use `private` for proof-local implementation details. Export and document declarations that form
  an intentional reusable API; a helper does not need to become public merely because another file
  might conceivably use it.
- Imports are the specific Mathlib files needed (`import Mathlib` only in scratch files).
  Dependency tools: `lake env lean scripts/ImportUsage.lean` computes, for every module, the
  imports its declarations actually use and a minimal import list (and lists NLAlib names that
  collide with Mathlib), written to `atlas/import_usage.json`; `python3 scripts/apply_imports.py`
  applies those suggestions (`--revert M …` restores a module's import block). Verify with
  `lake build` of the touched modules and their dependants.

## 3. Statements

- Index types: use finite types in matrix statements when they fit the mathematics and make the
  result reusable. `Fin` is also appropriate where an algorithm, recursion, sorted position, or
  dimension argument uses its structure. A dependency's current index type alone is not a reason
  either to restrict or generalize a statement.
- Norms (F4, 2026-10-13). `Matrix m n 𝕜` has no global norm in Mathlib; Mathlib offers four as
  scoped instances (`Matrix.Norms.Elementwise`, `.Operator`, `.Frobenius`, `.L2Operator`) and a
  signature cannot show which one is open. NLAlib therefore names its matrix norms: in a public
  statement a matrix norm is always one of `specNorm A` (spectral / L2 operator norm; needs
  `[DecidableEq n]` on the column index only), `frobNorm A`, `frobSq A` (`= frobNorm A ^ 2`),
  `nuclearNorm A` (`= schattenNorm A 1`), `schattenNorm A (p : ℝ≥0∞)` (including infinity),
  `kyFanNorm A k`. The finite real power-sum formula is `schattenNormReal A (p : ℝ)`;
  `schattenNorm_eq_of_ne_top` and `schattenNorm_ofReal` connect the main interface to this
  formula. Use the main interface for endpoint-inclusive statements. Retain bundled adapters
  such as `schattenSeminorm` and `schattenInvariantNorm` for Mathlib's generic norm APIs. The
  notation `‖A‖` applied to a matrix appears in statements only in `Matrix/Functions/`,
  `Matrix/OperatorTheory/` (C*-algebra and CFC files, under a file-level
  `open scoped Matrix.Norms.L2Operator`), in `ForMathlib/`, and in the two bridge lemmas
  `specNorm_eq_norm` (L2Operator scope) and `frobNorm_eq_norm` (Frobenius scope). No other file
  opens a `Matrix.Norms.*` scope at file level; a proof that needs Mathlib's normed API writes
  `open scoped Matrix.Norms.L2Operator in` before that one declaration and rewrites through the
  bridge (`scripts/check_norms.py`). The vector 2-norm is `‖WithLp.toLp 2 x‖` (Mathlib's
  `EuclideanSpace`, 𝕜-generic): squared norms are `‖WithLp.toLp 2 x‖ ^ 2`, unit vectors
  `‖WithLp.toLp 2 x‖ = 1`; `Real.sqrt (x ⬝ᵥ x)`, `{x // x ⬝ᵥ x = 1}` and `x ⬝ᵥ x` *as a norm* are
  not used in statements (`x ⬝ᵥ y` as a pairing is fine). Bridges:
  `norm_toLp_sq_eq_re_star_dotProduct` (𝕜), `norm_toLp_sq_eq_dotProduct_self` (ℝ), in
  `Matrix/Norms/Core.lean`.
- Condition number (F4). `conditionNumber (A : Matrix n n 𝕜) : ℝ≥0∞` is the textbook
  `‖A‖₂ ‖A⁻¹‖₂` for invertible `A` and `⊤` otherwise (`conditionNumber_of_isUnit`,
  `conditionNumber_eq_top_iff`, `one_le_conditionNumber`, `conditionNumber_eq_singularValues_ratio`);
  perturbation bounds take `(hA : IsUnit A)` and are stated with `(conditionNumber A).toReal`.
  The pseudoinverse quantity `‖A‖₂ ‖A⁺‖₂ = σ₁/σ_r` (0 at `A = 0`) is `moorePenroseConditionNumber A : ℝ`
  (any shape); it is not "the" condition number.
- Vocabulary (over `𝕜` unless marked ℝ): `frobInner A B` (the real part of the Frobenius pairing,
  `RCLike.re (∑ i, ∑ j, star (A i j) * B i j)`; the `𝕜`-valued pairing is `(Aᴴ * B).trace` and has
  no name); `HasOrthonormalCols Q := Qᴴ * Q = 1` and `projResidual Q A = A - Q * (Qᴴ * A)`
  (both in `Matrix/Basic/Orthonormal.lean`, upstream of `Norms`; every orthonormality hypothesis
  is `HasOrthonormalCols`, never a raw `Pᴴ * P = 1` or `Pᵀ * P = 1`; at ℝ a `Qᵀ * Q = 1` term
  elaborates against it, and a `Qᵀ * Q` goal is rewritten with `hQ.conjTranspose_mul_self` after
  `rw [← Matrix.conjTranspose_eq_transpose_of_trivial]`; `projResidual` is not the linear-system
  residual `b − Ax`); `columnSpace A` is the column range as a submodule and `rangeProjector A`
  is its matrix orthogonal projector (including rank-deficient and empty matrices); principal-angle
  APIs use the field-generic `directedSubspaceGap` and the real algebraic `overlapTangentNorm`,
  with guarded `tanThetaMax` for its geometric domain; `quadForm A z := star z ⬝ᵥ (A *ᵥ z)` (`𝕜`-valued, Mathlib's `PosSemidef`
  form; real consumers take `RCLike.re`, and over ℂ `0 ≤ quadForm A z` needs
  `open scoped ComplexOrder`) and
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
  `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`), with no `lamMin`; the smallest singular value
  of `A : Matrix m n 𝕜` with `card n ≤ card m` is `singularValues A (Fintype.card n - 1)`
  (variational form `singularValues_last_eq_iInf`), with no `sigmaMin`; `lambdaMax A` /
  `lambdaMin A := sSup / sInf (spectrum ℝ A)` over 𝕜 (bridges `lambdaMax_eq_eigenvalues₀_zero`,
  `lambdaMin_eq_eigenvalues₀_last` for Hermitian `A`; junk otherwise); the Loewner order `≤` (§2);
  PSD hypotheses are `A.PosSemidef` or `0 ≤ A`, never `0 ≤ lambdaMin A`;
  `gaussianMatrix m n` (a measure on `Matrix m n ℝ`, the push-forward of the i.i.d. product
  measure by `Matrix.of`) and `linForm c G` for its linear forms (coefficient array `c`, sample
  `G : Matrix m n ℝ`) (ℝ); `IsSubspaceEmbedding S U ε` (ℝ); `krylovSpace A b q` (over any field, as are
  `blockKrylovSpace` and `subspaceIterate`; the Krylov methods stay real); the matrix function
  `cfc f A` (Mathlib) with `matrixExp`, `matrixLog`, `traceExp`. Do not introduce a second spelling
  of any of these.
- Probability: an abstract space `{Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]`,
  random matrices as functions `X : Ω → Matrix m n 𝕜`, expectations as Bochner integrals.
  `Matrix m n α` carries the global product σ-algebra `Matrix.instMeasurableSpace` and, for a
  second-countable Borel `α`, the Borel instance `Matrix.instBorelSpace`
  (`ForMathlib/MeasureTheory/Matrix.lean`, with `Matrix.measurable_entry`,
  `Matrix.measurable_iff_entries`, `Matrix.ofMeasurableEquiv`, `Measurable.matrix_mul`); state
  measurability of a matrix-valued map as `Measurable T`, not entrywise. Laws are stated with
  Mathlib's `HasLaw X ν μ` (fields `.aemeasurable`, `.map_eq`), never as `μ.map X = …`: a standard
  Gaussian matrix is `HasLaw X (gaussianMatrix m n) μ`, a standard Gaussian vector
  `HasLaw x (gaussianVector n) μ`, a scalar `HasLaw g (gaussianReal 0 1) μ`, a Rademacher vector
  `HasLaw r (rademacherVector n) μ`, a sign `HasLaw r rademacherMeasure μ` (`gaussianVector n` and
  `rademacherVector n` are the product measures on `n → ℝ`; there are no `IsStandardGaussian` /
  `IsRademacher` abbreviations; `IsGaussian`/`HasGaussianLaw` for general Gaussian vectors are
  Mathlib's). A law hypothesis is never accompanied by the measurability or probability-measure
  facts it implies. Random signs are ℝ-valued (`±1`), never `Bool`. A theorem about `gaussianMatrix`
  itself integrates against it (the primary, most general form) and has a corollary
  `<name>_of_hasLaw` for a random matrix with that law in the same file; no `_of_map_eq` wrappers.
  Tails are failure probabilities `μ.real s ≤ c` (not `μ s ≤ ENNReal.ofReal c`, not
  `(μ s).toReal ≤ c`), when this is the natural form of the cited guarantee. Sketch-distribution
  theorems conclude `μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U ε} ≤ δ` (`docs/SKETCH_INTERFACE.md`).
  For probabilistic results, state the probability space and law or distributional assumptions
  that give the random object its meaning. Prefer Mathlib's `HasLaw` and measure-theoretic
  expectations when they make the theorem easier to apply. Finite sums, PMFs, recurrences, and
  specialized measures are valid interfaces when they are the natural computational form; provide
  bridges to the corresponding law or expectation when users need that connection. Where both a
  distribution-level result and a random-object corollary are useful, expose both. Orthonormality
  hypotheses are `HasOrthonormalCols V`. Prefer statements without integrability hypotheses
  (prove the `lintegral` form, then convert). `Matrix` has no global norm: Mathlib results that need
  a normed space on the sample space (Fernique, `HasGaussianLaw.map_fun`, `IsGaussian` of a product)
  are used under `open scoped Matrix.Norms.L2Operator` (whose topology is `Matrix`'s, so the Borel
  instance applies) or after flattening (`integral_gaussianMatrix_eq`, `gaussianMatrix_map_uncurry`).
- Prefer explicit constants when the source provides them or a useful refinement is available;
  existential constants and asymptotic bounds are appropriate when that is what the source proves
  or the useful theorem. Do not add precision that changes the theorem's content. Degenerate cases
  and side conditions must match the source or be stated and justified explicitly. Consider stating
  upper and lower bounds separately when that makes them easier to use; split a conjunction when
  its parts are useful independently, and keep a bundled result
  when the joint statement is the natural API. General form first, corollaries after. Definitions are total in Mathlib's
  style; the theorem, not the definition, carries the hypothesis that excludes the junk value
  (`IsUnit`, `DifferentiableAt`, …), and the docstring of the definition states the junk value.
  Hypotheses that follow from others are not taken (`(A + B).IsHermitian` next to `hA hB`;
  `Measurable g` next to `HasLaw g ν μ`). Spectral statements never quantify over Mathlib's
  chosen eigenvector basis (`hA.eigenvectorBasis i`) unless the basis is part of the mathematical
  construction; they may instead take an eigenvector `u` with
  `A *ᵥ u = c • u` and `‖WithLp.toLp 2 u‖ = 1`, and the extreme eigenvalue is `hA.eigenvalues₀ 0`
  or the last index. Cite the mathematical source when formalizing a published result, and preserve port attribution.
  For a helper or new bridge, explain its meaning and use; no artificial source citation is required.
- Every hypothesis explicit; no `axiom`, no `native_decide`; `sorry` only in a named scaffold
  (docstring `SCAFFOLD: <atlas id>`, catalogued).
- Deferred proofs may be developed in explicitly experimental modules, outside `import NLAlib`.
  Record them in `scripts/experimental_modules.txt`; the generated boundary excludes their import
  dependants. The strict default-import audit forbids `sorryAx` in every reachable declaration.
  A statement used provisionally as a scaffold or an explicit hypothesis must be checked with the
  same care as a proved one, since a wrong assumption propagates to every consumer. Do not label
  a result proved merely because its proof compiles against an unfinished dependency.
- State the mathematical specification before choosing a proof-friendly representation. Check
  degenerate cases, domains, dimensions, and side conditions against the source; do not weaken a
  theorem to make its proof convenient. Distinguish a proved specification from a theorem about a
  particular algorithm: algorithm guarantees need a bridge from the implementation or process to
  the specification, and their stated dimensions, failure conditions, and operation bounds must
  match what is actually established.

## 4. Docstrings

Every public declaration has a docstring whose first sentence says what it asserts. For a published
result, give the source and label (`HMT 2011, Thm 9.1`; `Tropp 2015, Thm 6.1.1`) and any deviation
from the printed statement (generalisation, different constant, side condition). For a ported proof,
preserve its origin (`ported from Prove2me solution GaussianMatrix.full_rank_ae`). Helpers and new
bridges explain their meaning and use; they do not need an invented source citation. A declaration
that is the formal statement of an atlas result ends with the tag line `atlas: <id>` (comma-separated
ids if several; `<id> (partial)` when it covers only part of the statement); a helper names the id
in prose only. The tag is machine-read: it is what links the declaration to the atlas.

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
lake build NLAlib NLAlib.Experimental
lake env lean scripts/AuditTrusted.lean   # default import: no sorry or nonstandard axioms
lake env lean scripts/Lint.lean           # standard declaration and instance checks
lake env lean scripts/Audit.lean          # experimental proof dependency inventory
lake env lean scripts/ExtractDecls.lean   # declaration index (+ atlas/external.json)
lake env lean Examples/Downstream.lean
lake env lean Examples/Probability.lean
python3 scripts/sync_atlas.py             # Lean side of atlas.json from the `atlas:` tags
python3 scripts/check_layers.py
python3 scripts/check_names.py            # naming conventions
python3 scripts/check_atlas.py
```

The declaration index and import inventory describe the current API. Historical migration
checklists are not acceptance criteria: assess mathematical generality and native interfaces
in the affected statements, and add focused downstream examples for new public contracts.
