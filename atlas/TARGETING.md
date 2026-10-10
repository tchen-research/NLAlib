# Targeting guide: choosing and stating RandNLA foundations

For people and agents adding to the RandNLA formalization. The goal is a library of
**foundations**: statements that other people's arguments cite, not end-to-end guarantees for
particular algorithms. A good target is small, is cited by many proofs, and is stated in a form
the next proof can use without rewriting.

The catalogue of candidates is `atlas.json`; the live map is https://research.chen.pw/NLAlib/.
Everything below is phrased against it.

## 1. How to pick a target

Score candidates in this order. Stop at the first one you can finish.

1. **Reuse.** Prefer results with high in-degree in the atlas dependency graph (the “used by”
   count in the viewer). A result consumed by three or more others beats one consumed by none.
2. **Unblocking.** Prefer results that are the open leaf under several `stated` or `assumed`
   items. Today the two biggest are Gaussian Lipschitz concentration and Gordon's theorem: proving
   them closes six open statements in Gaussian Random Matrices II–III and the LRA hypotheses.
3. **Prerequisites present.** Check `mathlib_prereqs` in the atlas entry. If a prerequisite is
   missing, the prerequisite is your target, not the result.
4. **One clean source.** Prefer a statement with a single textbook proof (the `sources` field)
   over one that needs several papers stitched together.
5. **Small statement, explicit constants.** A result whose statement fits in ten lines and names
   its constants is worth more than a sharper result with an existential constant.

Do **not** target, unless it is a mission capstone that a captain has asked for:
- `kind: application` entries (RSVD, Nyström, Hutch++, CG…). They consume foundations; the atlas
  lists them so you can see what a foundation unlocks.
- Anything an external Lean library already proves in the form we need, unless you are porting it
  (see §6).
- A statement that needs a definition that does not exist yet. Publish the definition first
  (§3).

### The first batches, in order

| Batch | Targets (atlas ids) | Why first |
|---|---|---|
| A. Matrix API | `norms-frob-spec`, `svd`, `eckart-young`, `weyl-mirsky`, `courant-fischer`, `pseudoinverse`, `orthonormal-completion`, `von-neumann-trace`, `hmt-9-1-spectral` | Used by everything downstream; three of them are currently hypotheses of the LRA theorems. |
| B. Gaussian closure | `gaussian-concentration`, `gordon`, then the six `stated` items they unblock | Finishes the Gaussian series; makes the LRA theorems unconditional. |
| C. Sketching | `ose-def`, `chi-square-upper-tail`, `jl-distributional`, `jl-lemma`, `gaussian-ose`, `matrix-chernoff-sampling`, `leverage-scores`, `leverage-sampling-ose` | The vocabulary of modern RandNLA; no Lean formalization of JL exists anywhere. |
| D. Estimation and Krylov basics | `hutchinson-unbiased`, `hutchinson-variance`, `spectral-measure`, `krylov-subspace`, `lanczos-recurrence`, `chebyshev-minimax`, `chebyshev-growth` | Small deterministic facts with high reuse in trace estimation and Lanczos analysis. |
| E. First complete algorithm | `randomized-kaczmarz` | One-page proof from projections and σ_min; a model for how consumers should look. |

## 2. How to state a result so it can be reused

The statement is the product. A proof can be replaced; a statement that nobody can apply is wasted.

**Objects.**
- Matrices are `Matrix (Fin m) (Fin n) ℝ`. Use `Fin` indices for anything that touches a Gaussian
  measure (the product measure is over `Fin p → Fin m → ℝ`). Purely algebraic lemmas may be stated
  over `[Fintype ι]` when that costs nothing.
- Norms: the spectral norm is Mathlib's `Matrix.Norms.L2Operator` instance (opened with
  `open scoped Matrix.Norms.L2Operator` or the local `specNorm`), the Frobenius norm is
  `Matrix.frobeniusNorm` or `frobSq` as an explicit sum. Do not introduce a third spelling.
- Gaussian matrices are `gaussianMatrix p m : Measure (Fin p → Fin m → ℝ)` from the
  `GaussianMatrix_basic` bundle, with `Matrix.of` as the matrix view. Connect to Mathlib's
  `stdGaussian` / `multivariateGaussian` with a transport lemma rather than redefining.
- Random objects on an abstract probability space: `{Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]`,
  random matrices as measurable functions, expectations as Bochner integrals `∫ ω, … ∂μ`.
- Order and functional calculus: `open scoped MatrixOrder`, `Matrix.PosSemidef`, `cfc`. No custom
  PSD predicate.
- Pseudoinverse: until the general Moore–Penrose definition exists, say which full-rank
  formula you mean (`pinvL`, `pinvR`) and state the `IsUnit` side condition explicitly.

**Shape.**
- Match the cited statement, including its degenerate cases. Mathlib's real division by zero is
  zero, so tail expressions are written piecewise where the source has a side condition.
- Every hypothesis explicit; no `axiom`, no `sorry`, no new `Prop` placeholders. If you must assume
  a cited fact, state it as a named `def … : Prop` hypothesis and record it in the atlas as
  `status: assumed`.
- Constants explicit (`Real.exp 1 ^ 2 * (p + r) / (2 * (p - r) ^ 2)`), never `∃ C`. If the
  source only gives an existential constant, derive and state a numeric one, and say in the
  explanation where it came from.
- Give the general form, then corollaries. A tail bound `∀ t ≥ 0, μ {…} ≤ …` is more reusable than
  an expectation bound; an expectation identity is more reusable than an inequality.
- Prefer two-sided statements split into two theorems (upper, lower) over one conjunction.

**Naming.** One namespace, `NLAlib`, with one file per concept (formerly one namespace per series; old:
`MatrixAnalysis`, `Sketching`, `Krylov`). Theorem names are snake_case and describe the
mathematics, not the source (`pinv_frobenius_moment`, not `tw_lemma_b2`). The atlas id is the
kebab-case version of the same words.

## 3. Definitions first

A definition bundle is the public interface of an area. Publish it as a `definition` item before
any theorem that uses it, and reuse it across the whole series (the way `GaussianMatrix_basic`
serves Gaussian Random Matrices I–III).

Bundles still to create, with what belongs in each:

- **`MatrixAnalysis_basic`**: block SVD (`svdBlocks A k`), truncated SVD `⟦A⟧_k`, singular values
  as a `Fin (min m n) → ℝ` descending sequence, Moore–Penrose pseudoinverse, `orth`/`residual`,
  orthonormal completion, nuclear norm.
- **`Sketching_basic`**: `IsSubspaceEmbedding S U ε`, `IsObliviousSubspaceEmbedding` (as a
  property of a measure on sketches), `leverageScore A i`, sampling-and-rescaling operators.
- **`Estimation_basic`**: isotropic test vectors, `hutchinson A z`, spectral measure `specMeasure A u`.
- **`Krylov_basic`**: `krylovSpace A b q`, Lanczos vectors and the Jacobi matrix, Chebyshev
  extremal quantities.

Before writing a definition: search Mathlib (loogle, `grep -r` in `.lake/packages/mathlib`) and this
library. If a faithful definition exists, use it and record it in `mathlib_prereqs`.

## 4. Workflow

1. Pick a target by §1. Note its atlas id.
2. Read its `sources` entry; the `label` is the theorem number to work from.
3. Check Mathlib (`grep`, loogle) and this library for existing statements. Record what you find
   in the atlas entry's `mathlib_prereqs` even if you stop here.
4. Open an issue titled with the atlas id and assign yourself; set the result's `status` to
   `planned` in `atlas/atlas.json`.
5. Write definitions needed (§3) into the area's `Basic.lean` (separate PR, label `api-change`),
   then the statement, then a natural-language read-back written from the Lean alone. If it does
   not match the source, fix the statement.
6. Prove it, or reduce it: for difficulty ≥ 4, state the result with the missing pieces as named
   hypotheses (`status: assumed`) and open issues for each piece, so the main statement lands
   early and the frontier is visible.
7. In the same PR update `atlas/atlas.json`:
   ```json
   "status": "proved",
   "formalizations": [{"library": "nlalib", "decl": "NLAlib.gordon", "status": "proved"}],
   "updated_at": "YYYY-MM-DD"
   ```
   CI validates it and redeploys the map on merge.
8. Add new `depends_on` edges you discovered while proving. The reuse ranking is only as good as
   the edges.

## 5. Quality bar

- Builds against the pinned toolchain with `lake build`; no `sorry`, no `admit`; axioms limited to
  `propext`, `Classical.choice`, `Quot.sound` (check with `#print axioms`).
- Statement read-back matches the source; deviations are written down in the submission
  explanation.
- Proof reuses platform theorems and Mathlib; no re-proving of something already Proved.
- The docstring names the source proof and says where the Lean proof departs from it.

## 6. External Lean libraries: port, do not depend

The package requires Mathlib only, so an external library is a **proof quarry**, never a
dependency. Porting rule: restate the result in our
conventions (§2), then translate the proof, citing the library and commit in the docstring (all
are Apache-2.0).

**HighDimProb** (dududuguo/HighDimProb, Lean v4.29.1, Mathlib v4.29.1; Reservoir shows it
failing to build on v4.31–v4.33). Useful because it uses Mathlib's own notions
(`HasSubgaussianMGF`, `iIndepFun`, `Matrix (Fin n) (Fin n) ℝ`), so translation is mostly renaming.

| HighDimProb result | Atlas target | Value |
|---|---|---|
| `HansonWright.hanson_wright_inequality_hdp_explicit_constant` (constant 1/(256e²)) | `hanson-wright` | High. Unlocks sub-Gaussian JL, trace-estimator tails, sub-Gaussian matrix norms. Single file of ~210 kB with its own `deterministicFrobeniusNorm` / `deterministicOperatorNorm` / `centeredQuadraticForm`, so budget for transport lemmas to Mathlib norms. |
| `coveringNumber_euclideanBall_le` | `epsilon-net-norm` | Medium. Crude bound (1 + 2R/ε)^n, but exactly what the ε-net argument needs. |
| `bernstein_sum_subExponential`, `hoeffding_sum_bounded` | `bernstein-scalar`, `hoeffding` | Medium. Check Mathlib first; Hoeffding's lemma in MGF form is already there. |
| `MatrixBernstein.*` | `matrix-bernstein` | None. Ours is already proved in `NLAlib/Concentration/Matrix/` with Tropp's constants. |
| Dudley, chaining, Gaussian functional tools | — | Not needed for current batches. |

Caveats: single maintainer, no sorry-free statement in the README, `Experimental` modules in flux.
Pin a commit when you port from it and record the commit in the docstring.

**Other quarries.** AI4SLT (Gaussian Lipschitz concentration via log-Sobolev) for
`gaussian-concentration`; the TR-01 companion repo for an SRHT variant; SparseStack for sparse
embeddings. Same rule applies.
