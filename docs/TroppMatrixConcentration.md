# Matrix Concentration Inequalities in Lean 4

> Provenance note (2026-10-09): this formalization now lives in `NLAlib/Concentration/Matrix/`
> (Defs, Laplace, Series, Chernoff, Bernstein, Intrinsic, OperatorConvexity) under the `NLAlib`
> namespace; the results table below gives the current `NLAlib` names and modules. The text that follows is the original
> README of the standalone project, kept for the mission links and the results table.

A Lean 4 / Mathlib formalization of the main results of Chapters 3–8 of

> Joel A. Tropp, *An Introduction to Matrix Concentration Inequalities*,
> Foundations and Trends in Machine Learning, 2015. [arXiv:1501.01571](https://arxiv.org/abs/1501.01571).

It covers the matrix Laplace transform method (Chapter 3), matrix Gaussian and Rademacher series (Chapter 4), the matrix Chernoff inequality (Chapter 5), the matrix Bernstein inequality (Chapter 6), the intrinsic-dimension refinements (Chapter 7), and Lieb's concavity theorem together with the operator-convexity toolkit behind it (Chapter 8). Every theorem is fully proved: the library contains no `sorry` and uses no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

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

- `spectralNorm` (the ℓ₂ operator norm), `lambdaMax`, `lambdaMin` (supremum and infimum of the real spectrum), `matrixExp`, `matrixLog` (via the continuous functional calculus), `traceExp`, and `LoewnerLE` (the semidefinite order).
- `hermitianSecondMoment`, `rectSecondMoment` (matrix variance statistics), `cumulantSum`, and the tail expressions `bernsteinTail`, `gaussianSeriesTail`, `chernoffLowerTail`, `chernoffUpperTail`.
- `dilation` (the Hermitian dilation of a rectangular matrix), `IsStandardGaussian`, `IsRademacher`, `intrinsicDimension`, `traceFunction`, and the Chapter 8 notions `matrixFunction`, `relativeEntropy` (matrix relative entropy), `OperatorConvexOn` (operator convexity), and `matrixPerspective`.

In NLAlib these live in `NLAlib/Concentration/Matrix/Defs/` (renamed 2026-10-09 from the
chapter-numbered files; map in `docs/renames/2026-10-09-housekeeping-H1.json`):

| Module | Contents |
|---|---|
| `NLAlib.Concentration.Matrix.Defs.Spectral` | `spectralNorm`, `lambdaMax`, `lambdaMin`, `matrixExp`, `matrixLog`, `traceExp`, `LoewnerLE` |
| `NLAlib.Concentration.Matrix.Defs.Dilation` | `dilation` |
| `NLAlib.Concentration.Matrix.Defs.Probability` | Borel instance on `Matrix m n ℂ`, `rectSecondMoment`, `hermitianSecondMoment`, `cumulantSum`, `bernsteinTail` |
| `NLAlib.Concentration.Matrix.Defs.ScalarLaws` (was `Ch4ScalarLaws`) | `IsStandardGaussian`, `IsRademacher`, `gaussianSeriesTail` |
| `NLAlib.Concentration.Matrix.Defs.ChernoffFunctions` (was `Ch5ChernoffFunctions`) | `chernoffCgfCoefficient`, `chernoffLowerTail`, `chernoffUpperTail` |
| `NLAlib.Concentration.Matrix.Defs.IntrinsicDimension` (was `Ch7Intrinsic`) | `intrinsicDimension`, `traceFunction` |
| `NLAlib.Concentration.Matrix.Defs.RelativeEntropy` (was `Ch8Entropy`) | `matrixFunction`, `relativeEntropy`, `OperatorConvexOn`, `matrixPerspective` |
| `NLAlib.Concentration.Matrix.Defs.JointTensor` (was `Ch8JointTensor`) | `jointTensorLeft`, `jointTensorRight`, `jointTensorVec`, `jointTensorEval` |
| `NLAlib.Concentration.Matrix.Defs.Calculus` | shared lemmas: `matrixExp_smul_eq_cfc`, `traceExp_smul_eq_sum`, `abs_le_norm_of_mem_spectrum`, reindexing (`reindexStarAlgEquiv`, `norm_reindex`, `lambdaMax_reindex`, `integral_reindex`), `dilationLinearMap`, `dilation_sq`, `integral_fromBlocks_diag` |

Random matrices are measurable functions into `Matrix (Fin d) (Fin d) ℂ` with the Borel σ-algebra, expectations are Bochner integrals for the operator norm, and the usual Lean conventions apply (real division by zero is zero, so the tail expressions are defined piecewise to match the source exactly in the degenerate cases).

## Results

Declaration names follow `docs/STANDARDS.md` §1 since 2026-10-09; the old chapter-prefixed names
are listed in `docs/renames/2026-10-09-concentration.json`.

| Chapter | Result | Lean declaration | Module |
|---|---|---|---|
| 3 | Hermitian exponential is positive definite and logarithm is its inverse | `NLAlib.posDef_matrixExp_and_matrixLog_matrixExp` | `NLAlib.Concentration.Matrix.Laplace.CgfExpLog` |
| 3 | Lieb replacement for an independent random matrix offset | `NLAlib.integral_traceExp_add_le_integral_traceExp_add_matrixLog` | `NLAlib.Concentration.Matrix.Laplace.CgfIndependentReplacement` |
| 3 | Integrability of extreme eigenvalues | `NLAlib.integrable_lambdaMax_and_lambdaMin` | `NLAlib.Concentration.Matrix.Laplace.ExpectExtremaIntegrable` |
| 3 | Proposition 3.2.2 — Expectation bounds for eigenvalues | `NLAlib.integral_lambdaMax_le_and_le_integral_lambdaMin` | `NLAlib.Concentration.Matrix.Laplace.LaplaceExpectations` |
| 3 | Proposition 3.2.1 — Tail bounds for eigenvalues | `NLAlib.measure_lambdaMax_ge_le_and_measure_lambdaMin_le_le` | `NLAlib.Concentration.Matrix.Laplace.LaplaceTails` |
| 3 | Expectation of an almost surely positive-definite matrix | `NLAlib.posDef_integral_of_ae_posDef` | `NLAlib.Concentration.Matrix.Laplace.LiebIntegralPosDef` |
| 3 | Jensen inequality on a nonclosed convex domain | `NLAlib.ConcaveOn.le_map_integral_of_integral_mem` | `NLAlib.Concentration.Matrix.Laplace.LiebJensen` |
| 3 | Exponential integrability survives a fixed Hermitian shift | `NLAlib.integrable_matrixExp_add_and_traceExp_add` | `NLAlib.Concentration.Matrix.Laplace.LiebRegularityShiftIntegrable` |
| 3 | Theorem 3.6.1 — Master expectation and tail bounds | `NLAlib.master_bounds` | `NLAlib.Concentration.Matrix.Laplace.MasterBounds` |
| 3 | Exponential integrability of an independent Hermitian sum | `NLAlib.integrable_matrixExp_smul_sum_of_iIndepFun` | `NLAlib.Concentration.Matrix.Laplace.MasterSumExponentialIntegrable` |
| 3 | Corollary 3.4.2 — Probabilistic Lieb inequality | `NLAlib.integral_traceExp_add_le_traceExp_add_matrixLog` | `NLAlib.Concentration.Matrix.Laplace.ProbabilisticLieb` |
| 3 | Trace exponential dominates exponentials of extremal eigenvalues | `NLAlib.exp_mul_lambdaMax_lambdaMin_le_traceExp_smul` | `NLAlib.Concentration.Matrix.Laplace.TailSpectralComparison` |
| 3 | Lemma 3.5.1 — Subadditivity of matrix cgfs | `NLAlib.trace_cgf_subadditivity` | `NLAlib.Concentration.Matrix.Laplace.TraceCgfSubadditivity` |
| 4 | Lemma 4.6.2 — Gaussian matrix mgf and cgf identities | `NLAlib.gaussian_matrix_mgf_cgf_eq` | `NLAlib.Concentration.Matrix.Series.GaussianMgfCgf` |
| 4 | Theorem 4.6.1 — Hermitian Gaussian and Rademacher series | `NLAlib.hermitian_gaussian_series` | `NLAlib.Concentration.Matrix.Series.HermitianSeries` |
| 4 | Theorem 4.1.1 — Matrix Gaussian and Rademacher series | `NLAlib.matrix_gaussian_series` | `NLAlib.Concentration.Matrix.Series.MatrixSeries` |
| 4 | Lemma 4.6.3 — Rademacher matrix mgf and cgf bounds | `NLAlib.rademacher_matrix_mgf_cgf_le` | `NLAlib.Concentration.Matrix.Series.RademacherMgfCgf` |
| 5 | Lemma 5.4.1 — Matrix Chernoff mgf and cgf bounds | `NLAlib.chernoff_matrix_mgf_cgf_le` | `NLAlib.Concentration.Matrix.Chernoff.ChernoffMgfCgf` |
| 5 | Theorem 5.1.1 — Matrix Chernoff, both spectral sides | `NLAlib.matrix_chernoff` | `NLAlib.Concentration.Matrix.Chernoff.MatrixChernoff` |
| 6 | Lemma 6.6.2 — Matrix Bernstein mgf and cgf bounds | `NLAlib.bernstein_matrix_mgf_cgf_le` | `NLAlib.Concentration.Matrix.Bernstein.BernsteinMgfCgf` |
| 6 | Equations 2.1.27–2.1.28 — Hermitian dilation identities | `NLAlib.dilation_identities` | `NLAlib.Concentration.Matrix.Bernstein.DilationIdentities` |
| 6 | Equation 2.2.10 — Variance statistic under dilation | `NLAlib.hermitianSecondMoment_dilation_eq_rectSecondMoment` | `NLAlib.Concentration.Matrix.Bernstein.DilationVariance` |
| 6 | Theorem 6.6.1 — Hermitian matrix Bernstein | `NLAlib.hermitian_bernstein` | `NLAlib.Concentration.Matrix.Bernstein.HermitianBernstein` |
| 6 | Second moment of an independent centered matrix sum: cross terms vanish | `NLAlib.integral_sum_mul_sum_eq_sum_integral_mul` | `NLAlib.Concentration.Matrix.Bernstein.IndependentSumSecondMoment` |
| 6 | Theorem 6.1.1 — Matrix Bernstein for rectangular matrices | `NLAlib.matrix_bernstein` | `NLAlib.Concentration.Matrix.Bernstein.MatrixBernstein` |
| 6 | Equation 2.2.5 — Additivity of matrix variance | `NLAlib.variance_additivity` | `NLAlib.Concentration.Matrix.Bernstein.VarianceAdditivity` |
| 7 | Equation 7.3.4 — Intrinsic dimension of variance blocks | `NLAlib.intrinsicDimension_fromBlocks` | `NLAlib.Concentration.Matrix.Intrinsic.BlockIntrinsic` |
| 7 | Proposition 7.4.1 — Generalized matrix Laplace transform | `NLAlib.measure_lambdaMax_ge_le_integral_traceFunction_div` | `NLAlib.Concentration.Matrix.Intrinsic.GeneralizedLaplace` |
| 7 | Theorem 7.3.1 — Intrinsic matrix Bernstein | `NLAlib.intrinsic_matrix_bernstein` | `NLAlib.Concentration.Matrix.Intrinsic.IntrinsicBernstein` |
| 7 | Corollary 7.3.2 — Intrinsic Bernstein expectation bound | `NLAlib.intrinsic_matrix_bernstein_expectation` | `NLAlib.Concentration.Matrix.Intrinsic.IntrinsicBernsteinExpectation` |
| 7 | Theorem 7.2.1 — Intrinsic matrix Chernoff | `NLAlib.intrinsic_matrix_chernoff` | `NLAlib.Concentration.Matrix.Intrinsic.IntrinsicChernoff` |
| 7 | Lemma 7.5.1 — Intrinsic dimension trace inequality | `NLAlib.traceFunction_le_intrinsicDimension_mul` | `NLAlib.Concentration.Matrix.Intrinsic.IntrinsicDimension` |
| 7 | Theorem 7.7.1 — Intrinsic Hermitian matrix Bernstein | `NLAlib.intrinsic_hermitian_bernstein` | `NLAlib.Concentration.Matrix.Intrinsic.IntrinsicHermitianBernstein` |
| 8 | Theorem 8.1.4 — Joint convexity of matrix relative entropy | `NLAlib.convexOn_relativeEntropy` | `NLAlib.Concentration.Matrix.OperatorConvexity.EntropyJointConvex` |
| 8 | Proposition 8.1.3 — Matrix relative entropy is nonnegative | `NLAlib.relativeEntropy_nonneg` | `NLAlib.Concentration.Matrix.OperatorConvexity.EntropyNonnegative` |
| 8 | Proposition 8.3.5 — Generalized Klein inequality | `NLAlib.generalized_klein` | `NLAlib.Concentration.Matrix.OperatorConvexity.GeneralizedKlein` |
| 8 | Functional calculus and spectrum of a block-diagonal Hermitian matrix | `NLAlib.matrixFunction_fromBlocks` | `NLAlib.Concentration.Matrix.OperatorConvexity.JensenBlockCalculus` |
| 8 | Operator convexity under isometric compression | `NLAlib.OperatorConvexOn.matrixFunction_conjTranspose_mul_mul_le` | `NLAlib.Concentration.Matrix.OperatorConvexity.JensenIsometricCompression` |
| 8 | Hermitian unitary dilation of an isometry | `NLAlib.isometry_reflection_identities` | `NLAlib.Concentration.Matrix.OperatorConvexity.JensenReflectionAlgebra` |
| 8 | Relative entropy as a tensor perspective | `NLAlib.relativeEntropy_eq_jointTensorEval_sub_trace` | `NLAlib.Concentration.Matrix.OperatorConvexity.JointTensorRepresentation` |
| 8 | Theorem 8.1.1 — Lieb concavity | `NLAlib.lieb_concavity` | `NLAlib.Concentration.Matrix.OperatorConvexity.LiebConcavity` |
| 8 | Proposition 8.4.8 — Logarithm is operator concave | `NLAlib.operatorConvexOn_neg_log` | `NLAlib.Concentration.Matrix.OperatorConvexity.LogOperatorConcave` |
| 8 | Proposition 8.4.4 — Logarithm is operator monotone | `NLAlib.matrixLog_le_matrixLog` | `NLAlib.Concentration.Matrix.OperatorConvexity.LogOperatorMonotone` |
| 8 | Theorem 8.5.2 — Operator Jensen inequality | `NLAlib.operator_jensen` | `NLAlib.Concentration.Matrix.OperatorConvexity.OperatorJensen` |
| 8 | Theorem 8.6.2 — Matrix perspective is jointly operator convex | `NLAlib.matrixPerspective_jointly_operatorConvex` | `NLAlib.Concentration.Matrix.OperatorConvexity.PerspectiveConvex` |
| 8 | Square-root and inverse-square-root identities for positive definite matrices | `NLAlib.matrixFunction_sqrt_identities` | `NLAlib.Concentration.Matrix.OperatorConvexity.PerspectiveSqrtNormalization` |
| 8 | Example 8.3.4 — Trace exponential is monotone | `NLAlib.traceExp_le_traceExp` | `NLAlib.Concentration.Matrix.OperatorConvexity.TraceExpMonotone` |
| 8 | Lemma 8.1.6 — Attained variational formula for trace | `NLAlib.isGreatest_variational_trace` | `NLAlib.Concentration.Matrix.OperatorConvexity.VariationalTrace` |
| 8 | Equation 8.1.2 — Variational trace exponential | `NLAlib.isGreatest_variational_traceExp` | `NLAlib.Concentration.Matrix.OperatorConvexity.VariationalTraceExp` |

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
