# Matrix Concentration Inequalities in Lean 4

> Current layout (2026-10-13): deterministic matrix-function and operator-convexity theory lives
> in `NLAlib/Matrix/Functions/`. Expectations, MGFs and concentration bounds live in
> `NLAlib/Probability/Concentration/`. The results table below uses current module paths;
> the mission links preserve the provenance of the original standalone project.

A Lean 4 / Mathlib formalization of the main results of Chapters 3–8 of

> Joel A. Tropp, *An Introduction to Matrix Concentration Inequalities*,
> Foundations and Trends in Machine Learning, 2015. [arXiv:1501.01571](https://arxiv.org/abs/1501.01571).

It covers the matrix Laplace transform method (Chapter 3), matrix Gaussian and Rademacher series (Chapter 4), the matrix Chernoff inequality (Chapter 5), the matrix Bernstein inequality (Chapter 6), the intrinsic-dimension refinements (Chapter 7), and Lieb's concavity theorem together with the operator-convexity toolkit behind it (Chapter 8). NLAlib audits its default import for unfinished proofs and nonstandard axioms; the separate `NLAlib.Experimental` import includes explicitly unfinished developments. Consult the declaration index for each theorem's transitive proof status.

## How this was made

This formalization was carried out on [Prove2me](https://prove2.me), a platform where theorems are stated as missions and proofs are verified against a pinned Mathlib by a Lean server. The work is organized as six missions, one per chapter, and every statement here is Proved there:

- [Ch 3: Matrix Laplace Transform](https://prove2.me/missions/An_Introduction_to_Matrix_Concentration_Inequalities_Ch_3%3A_Matrix_Laplace_Transform)
- [Ch 4: Gaussian and Rademacher Series](https://prove2.me/missions/An_Introduction_to_Matrix_Concentration_Inequalities_Ch_4%3A_Gaussian_and_Rademacher_Series)
- [Ch 5: Matrix Chernoff](https://prove2.me/missions/An_Introduction_to_Matrix_Concentration_Inequalities_Ch_5%3A_Matrix_Chernoff)
- [Ch 6: Matrix Bernstein](https://prove2.me/missions/An_Introduction_to_Matrix_Concentration_Inequalities_Ch_6%3A_Matrix_Bernstein)
- [Ch 7: Intrinsic Dimension](https://prove2.me/missions/An_Introduction_to_Matrix_Concentration_Inequalities_Ch_7%3A_Intrinsic_Dimension)
- [Ch 8: Lieb’s Concavity](https://prove2.me/missions/An_Introduction_to_Matrix_Concentration_Inequalities_Ch_8%3A_Lieb%E2%80%99s_Concavity)

The Lean statements and proofs were produced with large language models (Anthropic's Claude, driven through Claude Code, and OpenAI's Codex), with me curating the targets and reviewing the results. The models worked from Tropp's text and translated its proofs; where a proof deviates from the printed argument, that is noted in the explanation attached to the corresponding Prove2me submission. Everything in this repository has been machine-checked by Lean 4 against Mathlib, both locally and by the Prove2me verifier, so the mathematical content does not rest on trusting the models.

## Layout

```
TroppMatrixConcentration.lean        -- imports every module
TroppMatrixConcentration/
  Defs/                              -- definitions shared across chapters
  Ch3/ Ch4/ Ch5/ Ch6/ Ch7/ Ch8/      -- one module per theorem
```

All declarations live in the namespace `TroppMatrixConcentration`. The main definitions (in `Defs/`) are:

- `lambdaMax`, `lambdaMin` (supremum and infimum of the real spectrum), `matrixExp`, `matrixLog` (via the continuous functional calculus) and `traceExp`. The spectral norm is Mathlib's `‖A‖` under `open scoped Matrix.Norms.L2Operator` and the semidefinite order is Mathlib's `A ≤ B` under `open scoped MatrixOrder` (`Matrix.le_iff`); the former `spectralNorm` and `LoewnerLE` were retired in the 2026-10-12 dedup round.
- `hermitianSecondMoment`, `rectSecondMoment` (matrix variance statistics), `cumulantSum`, and the tail expressions `bernsteinTail`, `gaussianSeriesTail`, `chernoffLowerTail`, `chernoffUpperTail`.
- `dilation` (the Hermitian dilation of a rectangular matrix), `IsStandardGaussian`, `IsRademacher`, `intrinsicDimension`, `traceFunction`, and the Chapter 8 notions `relativeEntropy` (matrix relative entropy), `OperatorConvexOn` (operator convexity), and `matrixPerspective`. The matrix function `f(A)` of a Hermitian matrix is Mathlib's `cfc f A` (the former `matrixFunction` was retired in the 2026-10-12 dedup round; its lemmas are now `cfc_*`), and `matrixLog A = CFC.log A` by `rfl` (`matrixLog_eq_log`).

In NLAlib these live in the modules below (renamed 2026-10-09 from the chapter-numbered files,
map in `docs/renames/2026-10-09-housekeeping-H1.json`; the deterministic ones moved to the Matrix
layer in the 2026-10-12 dedup round, maps in `docs/renames/2026-10-12-dedup-*.json`):

| Module | Contents |
|---|---|
| `NLAlib.Matrix.Spectral.Core` | `lambdaMax`, `lambdaMin` |
| `NLAlib.Matrix.Functions.ExpLog` | `matrixExp`, `matrixLog`, `traceExp` |
| `NLAlib.Matrix.Basic.Dilation` | `dilation` |
| `NLAlib.ForMathlib.MeasureTheory.Matrix` | product measurable and Borel structure on matrices |
| `NLAlib.Probability.Concentration.Basic.MatrixStatistics` | `rectSecondMoment`, `hermitianSecondMoment`, `cumulantSum`, `bernsteinTail` |
| `NLAlib.Probability.Concentration.Basic.ScalarLaws` (was `Ch4ScalarLaws`) | `gaussianSeriesTail`; scalar distributions use Mathlib's `HasLaw` |
| `NLAlib.Probability.Concentration.Basic.ChernoffFunctions` (was `Ch5ChernoffFunctions`) | `chernoffCgfCoefficient`, `chernoffLowerTail`, `chernoffUpperTail` |
| `NLAlib.Matrix.Functions.IntrinsicDimension` (was `Ch7Intrinsic`) | `intrinsicDimension`, `traceFunction` |
| `NLAlib.Matrix.Functions.Basic` (was `Ch8Entropy`) | `relativeEntropy`, `OperatorConvexOn`, `matrixPerspective` |
| `NLAlib.Matrix.Functions.JointTensor` (was `Ch8JointTensor`) | `jointTensorLeft`, `jointTensorRight`, `jointTensorVec`, `jointTensorEval` |
| `NLAlib.Matrix.Functions.HermitianCalculus` | shared deterministic lemmas: `matrixExp_smul_eq_cfc`, `traceExp_smul_eq_sum`, `abs_le_norm_of_mem_spectrum`, reindexing (`reindexStarAlgEquiv`, `norm_reindex`, `spectrum_reindex`, `lambdaMax_reindex`), `dilationLinearMap`, `dilation_sq`, block-diagonal positivity and norm (`posSemidef_fromBlocks_diag`, `norm_fromBlocks_diag`) |
| `NLAlib.Probability.Concentration.Basic.MatrixCalculus` | the integral lemmas `integral_reindex`, `integral_fromBlocks_diag` |

Random matrices are measurable functions into `Matrix (Fin d) (Fin d) ℂ` with the Borel σ-algebra, expectations are Bochner integrals for the operator norm, and the usual Lean conventions apply (real division by zero is zero, so the tail expressions are defined piecewise to match the source exactly in the degenerate cases).

## Results

Declaration names follow `docs/STANDARDS.md` §1 since 2026-10-09; the old chapter-prefixed names
are listed in `docs/renames/2026-10-09-concentration.json`.

| Chapter | Result | Lean declaration | Module |
|---|---|---|---|
| 3 | Hermitian exponential is positive definite and logarithm is its inverse | `NLAlib.posDef_matrixExp_and_matrixLog_matrixExp` | `NLAlib.Matrix.Functions.ExpLogPosDef` |
| 3 | Lieb replacement for an independent random matrix offset | `NLAlib.integral_traceExp_add_le_integral_traceExp_add_matrixLog` | `NLAlib.Probability.Concentration.Matrix.CgfIndependentReplacement` |
| 3 | Integrability of extreme eigenvalues | `NLAlib.integrable_lambdaMax_and_lambdaMin` | `NLAlib.Probability.Concentration.Matrix.ExpectExtremaIntegrable` |
| 3 | Proposition 3.2.2 — Expectation bounds for eigenvalues | `NLAlib.integral_lambdaMax_le_and_le_integral_lambdaMin` | `NLAlib.Probability.Concentration.Matrix.LaplaceExpectations` |
| 3 | Proposition 3.2.1 — Tail bounds for eigenvalues | `NLAlib.measure_lambdaMax_ge_le_and_measure_lambdaMin_le_le` | `NLAlib.Probability.Concentration.Matrix.LaplaceTails` |
| 3 | Expectation of an almost surely positive-definite matrix | `NLAlib.posDef_integral_of_ae_posDef` | `NLAlib.Probability.Concentration.Matrix.LiebIntegralPosDef` |
| 3 | Jensen inequality on a nonclosed convex domain | `ConcaveOn.le_map_integral_of_integral_mem` | `NLAlib.ForMathlib.Analysis.Convex.Integral` |
| 3 | Exponential integrability survives a fixed Hermitian shift | `NLAlib.integrable_matrixExp_add_and_traceExp_add` | `NLAlib.Probability.Concentration.Matrix.LiebRegularityShiftIntegrable` |
| 3 | Theorem 3.6.1 — Master expectation and tail bounds | `NLAlib.master_bounds` | `NLAlib.Probability.Concentration.Matrix.MasterBounds` |
| 3 | Exponential integrability of an independent Hermitian sum | `NLAlib.integrable_matrixExp_smul_sum_of_iIndepFun` | `NLAlib.Probability.Concentration.Matrix.MasterSumExponentialIntegrable` |
| 3 | Corollary 3.4.2 — Probabilistic Lieb inequality | `NLAlib.integral_traceExp_add_le_traceExp_add_matrixLog` | `NLAlib.Probability.Concentration.Matrix.ProbabilisticLieb` |
| 3 | Trace exponential dominates exponentials of extremal eigenvalues | `NLAlib.exp_mul_lambdaMax_lambdaMin_le_traceExp_smul` | `NLAlib.Matrix.Functions.TraceExpBounds` |
| 3 | Lemma 3.5.1 — Subadditivity of matrix cgfs | `NLAlib.trace_cgf_subadditivity` | `NLAlib.Probability.Concentration.Matrix.TraceCgfSubadditivity` |
| 4 | Lemma 4.6.2 — Gaussian matrix mgf and cgf identities | `NLAlib.gaussian_matrix_mgf_cgf_eq` | `NLAlib.Probability.Concentration.Matrix.GaussianMgfCgf` |
| 4 | Theorem 4.6.1 — Hermitian Gaussian and Rademacher series | `NLAlib.hermitian_gaussian_series` | `NLAlib.Probability.Concentration.Matrix.HermitianSeries` |
| 4 | Theorem 4.1.1 — Matrix Gaussian and Rademacher series | `NLAlib.matrix_gaussian_series` | `NLAlib.Probability.Concentration.Matrix.MatrixSeries` |
| 4 | Lemma 4.6.3 — Rademacher matrix mgf and cgf bounds | `NLAlib.rademacher_matrix_mgf_cgf_le` | `NLAlib.Probability.Concentration.Matrix.RademacherMgfCgf` |
| 5 | Lemma 5.4.1 — Matrix Chernoff mgf and cgf bounds | `NLAlib.chernoff_matrix_mgf_cgf_le` | `NLAlib.Probability.Concentration.Matrix.ChernoffMgfCgf` |
| 5 | Theorem 5.1.1 — Matrix Chernoff, both spectral sides | `NLAlib.matrix_chernoff` | `NLAlib.Probability.Concentration.Matrix.MatrixChernoff` |
| 6 | Lemma 6.6.2 — Matrix Bernstein mgf and cgf bounds | `NLAlib.bernstein_matrix_mgf_cgf_le` | `NLAlib.Probability.Concentration.Matrix.BernsteinMgfCgf` |
| 6 | Equations 2.1.27–2.1.28 — Hermitian dilation identities | `NLAlib.dilation_identities` | `NLAlib.Matrix.Functions.DilationIdentities` |
| 6 | Equation 2.2.10 — Variance statistic under dilation | `NLAlib.hermitianSecondMoment_dilation_eq_rectSecondMoment` | `NLAlib.Probability.Concentration.Matrix.DilationVariance` |
| 6 | Theorem 6.6.1 — Hermitian matrix Bernstein | `NLAlib.hermitian_bernstein` | `NLAlib.Probability.Concentration.Matrix.HermitianBernstein` |
| 6 | Second moment of an independent centered matrix sum: cross terms vanish | `NLAlib.integral_sum_mul_sum_eq_sum_integral_mul` | `NLAlib.Probability.Concentration.Matrix.IndependentSumSecondMoment` |
| 6 | Theorem 6.1.1 — Matrix Bernstein for rectangular matrices | `NLAlib.matrix_bernstein` | `NLAlib.Probability.Concentration.Matrix.MatrixBernstein` |
| 6 | Equation 2.2.5 — Additivity of matrix variance | `NLAlib.variance_additivity` | `NLAlib.Probability.Concentration.Matrix.VarianceAdditivity` |
| 7 | Equation 7.3.4 — Intrinsic dimension of variance blocks | `NLAlib.intrinsicDimension_fromBlocks` | `NLAlib.Matrix.Functions.IntrinsicDimension` |
| 7 | Proposition 7.4.1 — Generalized matrix Laplace transform | `NLAlib.measure_lambdaMax_ge_le_integral_traceFunction_div` | `NLAlib.Probability.Concentration.Matrix.GeneralizedLaplace` |
| 7 | Theorem 7.3.1 — Intrinsic matrix Bernstein | `NLAlib.intrinsic_matrix_bernstein` | `NLAlib.Probability.Concentration.Matrix.IntrinsicBernstein` |
| 7 | Corollary 7.3.2 — Intrinsic Bernstein expectation bound | `NLAlib.intrinsic_matrix_bernstein_expectation` | `NLAlib.Probability.Concentration.Matrix.IntrinsicBernsteinExpectation` |
| 7 | Theorem 7.2.1 — Intrinsic matrix Chernoff | `NLAlib.intrinsic_matrix_chernoff` | `NLAlib.Probability.Concentration.Matrix.IntrinsicChernoff` |
| 7 | Lemma 7.5.1 — Intrinsic dimension trace inequality | `NLAlib.traceFunction_le_intrinsicDimension_mul` | `NLAlib.Matrix.Functions.IntrinsicDimension` |
| 7 | Theorem 7.7.1 — Intrinsic Hermitian matrix Bernstein | `NLAlib.intrinsic_hermitian_bernstein` | `NLAlib.Probability.Concentration.Matrix.IntrinsicHermitianBernstein` |
| 8 | Theorem 8.1.4 — Joint convexity of matrix relative entropy | `NLAlib.convexOn_relativeEntropy` | `NLAlib.Matrix.Functions.EntropyJointConvex` |
| 8 | Proposition 8.1.3 — Matrix relative entropy is nonnegative | `NLAlib.relativeEntropy_nonneg` | `NLAlib.Matrix.Functions.EntropyNonnegative` |
| 8 | Proposition 8.3.5 — Generalized Klein inequality | `NLAlib.generalized_klein` | `NLAlib.Matrix.Functions.GeneralizedKlein` |
| 8 | Functional calculus and spectrum of a block-diagonal Hermitian matrix | `NLAlib.cfc_fromBlocks` | `NLAlib.Matrix.Functions.JensenBlockCalculus` |
| 8 | Operator convexity under isometric compression | `NLAlib.OperatorConvexOn.cfc_conjTranspose_mul_mul_le` | `NLAlib.Matrix.Functions.JensenIsometricCompression` |
| 8 | Hermitian unitary dilation of an isometry | `NLAlib.isometry_reflection_identities` | `NLAlib.Matrix.Functions.JensenReflectionAlgebra` |
| 8 | Relative entropy as a tensor perspective | `NLAlib.relativeEntropy_eq_jointTensorEval_sub_trace` | `NLAlib.Matrix.Functions.JointTensorRepresentation` |
| 8 | Theorem 8.1.1 — Lieb concavity (any finite index type) | `NLAlib.lieb_concavity` | `NLAlib.Matrix.Functions.LiebConcavity` |
| 8 | Proposition 8.4.8 — Logarithm is operator concave | `NLAlib.operatorConvexOn_neg_log` | `NLAlib.Matrix.Functions.LogOperatorConcave` |
| 8 | Proposition 8.4.4 — Logarithm is operator monotone | Mathlib `CFC.log_monotoneOn` (the NLAlib copy `matrixLog_le_matrixLog` was retired 2026-10-12) | Mathlib `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order` |
| 8 | Theorem 8.5.2 — Operator Jensen inequality | `NLAlib.operator_jensen` | `NLAlib.Matrix.Functions.OperatorJensen` |
| 8 | Theorem 8.6.2 — Matrix perspective is jointly operator convex | `NLAlib.matrixPerspective_jointly_operatorConvex` | `NLAlib.Matrix.Functions.PerspectiveConvex` |
| 8 | Square-root and inverse-square-root identities for positive definite matrices | `NLAlib.cfc_sqrt_identities` | `NLAlib.Matrix.Functions.PerspectiveSqrtNormalization` |
| 8 | Example 8.3.4 — Trace exponential is monotone | `NLAlib.traceExp_le_traceExp` | `NLAlib.Matrix.Functions.TraceExpMonotone` |
| 8 | Lemma 8.1.6 — Attained variational formula for trace | `NLAlib.isGreatest_variational_trace` | `NLAlib.Matrix.Functions.VariationalTrace` |
| 8 | Equation 8.1.2 — Variational trace exponential | `NLAlib.isGreatest_variational_traceExp` | `NLAlib.Matrix.Functions.VariationalTraceExp` |

## Building

The project pins Lean `v4.33.1` and the Mathlib commit recorded in `lake-manifest.json`.
Run the following commands from this project's `TroppMatrixConcentrationLean/`
folder, or open this folder as your Lean editor workspace.

```
lake exe cache get
lake build
```

## License

Apache License 2.0, see [LICENSE](../LICENSE).
