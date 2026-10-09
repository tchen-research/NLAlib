# Matrix Concentration Inequalities in Lean 4

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

- `spectralNorm` (the ℓ₂ operator norm), `lambdaMax`, `lambdaMin` (supremum and infimum of the real spectrum), `matrixExp`, `matrixLog` (via the continuous functional calculus), `traceExp`, and `loewnerLE` (the semidefinite order).
- `hermitianSecondMoment`, `rectSecondMoment` (matrix variance statistics), `cumulantSum`, and the tail expressions `bernsteinTail`, `gaussianSeriesTail`, `chernoffLowerTail`, `chernoffUpperTail`.
- `dilation` (the Hermitian dilation of a rectangular matrix), `standardGaussianLaw`, `rademacherLaw`, `intrinsicDimension`, `traceFunction`, and the Chapter 8 notions of matrix relative entropy, operator convexity, and the matrix perspective.

Random matrices are measurable functions into `Matrix (Fin d) (Fin d) ℂ` with the Borel σ-algebra, expectations are Bochner integrals for the operator norm, and the usual Lean conventions apply (real division by zero is zero, so the tail expressions are defined piecewise to match the source exactly in the degenerate cases).

## Results

| Chapter | Result | Lean declaration | Module |
|---|---|---|---|
| 3 | Hermitian exponential is positive definite and logarithm is its inverse | `TroppMatrixConcentration.ch3_cgf_exp_log` | `Ch3.CgfExpLog` |
| 3 | Lieb replacement for an independent random matrix offset | `TroppMatrixConcentration.ch3_cgf_independent_replacement` | `Ch3.CgfIndependentReplacement` |
| 3 | Integrability of extreme eigenvalues | `TroppMatrixConcentration.ch3_expect_extrema_integrable` | `Ch3.ExpectExtremaIntegrable` |
| 3 | Proposition 3.2.2 — Expectation bounds for eigenvalues | `TroppMatrixConcentration.ch3_laplace_expectations` | `Ch3.LaplaceExpectations` |
| 3 | Proposition 3.2.1 — Tail bounds for eigenvalues | `TroppMatrixConcentration.ch3_laplace_tails` | `Ch3.LaplaceTails` |
| 3 | Expectation of an almost surely positive-definite matrix | `TroppMatrixConcentration.ch3_lieb_integral_posDef` | `Ch3.LiebIntegralPosDef` |
| 3 | Jensen inequality on a nonclosed convex domain | `TroppMatrixConcentration.ch3_lieb_jensen` | `Ch3.LiebJensen` |
| 3 | Exponential integrability survives a fixed Hermitian shift | `TroppMatrixConcentration.ch3_lieb_regularity_shift_integrable` | `Ch3.LiebRegularityShiftIntegrable` |
| 3 | Theorem 3.6.1 — Master expectation and tail bounds | `TroppMatrixConcentration.master_bounds` | `Ch3.MasterBounds` |
| 3 | Exponential integrability of an independent Hermitian sum | `TroppMatrixConcentration.ch3_master_sum_exponential_integrable` | `Ch3.MasterSumExponentialIntegrable` |
| 3 | Corollary 3.4.2 — Probabilistic Lieb inequality | `TroppMatrixConcentration.ch3_probabilistic_lieb` | `Ch3.ProbabilisticLieb` |
| 3 | Trace exponential dominates exponentials of extremal eigenvalues | `TroppMatrixConcentration.ch3_tail_spectral_comparison` | `Ch3.TailSpectralComparison` |
| 3 | Lemma 3.5.1 — Subadditivity of matrix cgfs | `TroppMatrixConcentration.trace_cgf_subadditivity` | `Ch3.TraceCgfSubadditivity` |
| 4 | Lemma 4.6.2 — Gaussian matrix mgf and cgf identities | `TroppMatrixConcentration.ch4_gaussian_mgf_cgf` | `Ch4.GaussianMgfCgf` |
| 4 | Theorem 4.6.1 — Hermitian Gaussian and Rademacher series | `TroppMatrixConcentration.ch4_hermitian_series` | `Ch4.HermitianSeries` |
| 4 | Theorem 4.1.1 — Matrix Gaussian and Rademacher series | `TroppMatrixConcentration.ch4_matrix_series` | `Ch4.MatrixSeries` |
| 4 | Lemma 4.6.3 — Rademacher matrix mgf and cgf bounds | `TroppMatrixConcentration.ch4_rademacher_mgf_cgf` | `Ch4.RademacherMgfCgf` |
| 5 | Lemma 5.4.1 — Matrix Chernoff mgf and cgf bounds | `TroppMatrixConcentration.ch5_chernoff_mgf_cgf` | `Ch5.ChernoffMgfCgf` |
| 5 | Theorem 5.1.1 — Matrix Chernoff, both spectral sides | `TroppMatrixConcentration.ch5_matrix_chernoff` | `Ch5.MatrixChernoff` |
| 6 | Lemma 6.6.2 — Matrix Bernstein mgf and cgf bounds | `TroppMatrixConcentration.bernstein_mgf_cgf` | `Ch6.BernsteinMgfCgf` |
| 6 | Equations 2.1.27–2.1.28 — Hermitian dilation identities | `TroppMatrixConcentration.dilation_identities` | `Ch6.DilationIdentities` |
| 6 | Equation 2.2.10 — Variance statistic under dilation | `TroppMatrixConcentration.dilation_variance` | `Ch6.DilationVariance` |
| 6 | Theorem 6.6.1 — Hermitian matrix Bernstein | `TroppMatrixConcentration.hermitian_bernstein` | `Ch6.HermitianBernstein` |
| 6 | Second moment of an independent centered matrix sum: cross terms vanish | `TroppMatrixConcentration.ch6_independent_sum_second_moment` | `Ch6.IndependentSumSecondMoment` |
| 6 | Theorem 6.1.1 — Matrix Bernstein for rectangular matrices | `TroppMatrixConcentration.matrix_bernstein` | `Ch6.MatrixBernstein` |
| 6 | Equation 2.2.5 — Additivity of matrix variance | `TroppMatrixConcentration.variance_additivity` | `Ch6.VarianceAdditivity` |
| 7 | Equation 7.3.4 — Intrinsic dimension of variance blocks | `TroppMatrixConcentration.ch7_block_intrinsic` | `Ch7.BlockIntrinsic` |
| 7 | Proposition 7.4.1 — Generalized matrix Laplace transform | `TroppMatrixConcentration.ch7_generalized_laplace` | `Ch7.GeneralizedLaplace` |
| 7 | Theorem 7.3.1 — Intrinsic matrix Bernstein | `TroppMatrixConcentration.ch7_intrinsic_bernstein` | `Ch7.IntrinsicBernstein` |
| 7 | Corollary 7.3.2 — Intrinsic Bernstein expectation bound | `TroppMatrixConcentration.ch7_intrinsic_bernstein_expectation` | `Ch7.IntrinsicBernsteinExpectation` |
| 7 | Theorem 7.2.1 — Intrinsic matrix Chernoff | `TroppMatrixConcentration.ch7_intrinsic_chernoff` | `Ch7.IntrinsicChernoff` |
| 7 | Lemma 7.5.1 — Intrinsic dimension trace inequality | `TroppMatrixConcentration.ch7_intrinsic_dimension` | `Ch7.IntrinsicDimension` |
| 7 | Theorem 7.7.1 — Intrinsic Hermitian matrix Bernstein | `TroppMatrixConcentration.ch7_intrinsic_hermitian_bernstein` | `Ch7.IntrinsicHermitianBernstein` |
| 8 | Theorem 8.1.4 — Joint convexity of matrix relative entropy | `TroppMatrixConcentration.ch8_entropy_joint_convex` | `Ch8.EntropyJointConvex` |
| 8 | Proposition 8.1.3 — Matrix relative entropy is nonnegative | `TroppMatrixConcentration.ch8_entropy_nonnegative` | `Ch8.EntropyNonnegative` |
| 8 | Proposition 8.3.5 — Generalized Klein inequality | `TroppMatrixConcentration.ch8_generalized_klein` | `Ch8.GeneralizedKlein` |
| 8 | Functional calculus and spectrum of a block-diagonal Hermitian matrix | `TroppMatrixConcentration.ch8_jensen_block_calculus` | `Ch8.JensenBlockCalculus` |
| 8 | Operator convexity under isometric compression | `TroppMatrixConcentration.ch8_jensen_isometric_compression` | `Ch8.JensenIsometricCompression` |
| 8 | ch8_jensen_reflection_algebra | `TroppMatrixConcentration.ch8_jensen_reflection_algebra` | `Ch8.JensenReflectionAlgebra` |
| 8 | Relative entropy as a tensor perspective | `TroppMatrixConcentration.ch8_joint_tensor_representation` | `Ch8.JointTensorRepresentation` |
| 8 | Theorem 8.1.1 — Lieb concavity | `TroppMatrixConcentration.lieb_concavity` | `Ch8.LiebConcavity` |
| 8 | Proposition 8.4.8 — Logarithm is operator concave | `TroppMatrixConcentration.ch8_log_operator_concave` | `Ch8.LogOperatorConcave` |
| 8 | Proposition 8.4.4 — Logarithm is operator monotone | `TroppMatrixConcentration.ch8_log_operator_monotone` | `Ch8.LogOperatorMonotone` |
| 8 | Theorem 8.5.2 — Operator Jensen inequality | `TroppMatrixConcentration.ch8_operator_jensen` | `Ch8.OperatorJensen` |
| 8 | Theorem 8.6.2 — Matrix perspective is jointly operator convex | `TroppMatrixConcentration.ch8_perspective_convex` | `Ch8.PerspectiveConvex` |
| 8 | Square-root and inverse-square-root identities for positive definite matrices | `TroppMatrixConcentration.ch8_perspective_sqrt_normalization` | `Ch8.PerspectiveSqrtNormalization` |
| 8 | Example 8.3.4 — Trace exponential is monotone | `TroppMatrixConcentration.ch8_trace_exp_monotone` | `Ch8.TraceExpMonotone` |
| 8 | Lemma 8.1.6 — Attained variational formula for trace | `TroppMatrixConcentration.ch8_variational_trace` | `Ch8.VariationalTrace` |
| 8 | Equation 8.1.2 — Variational trace exponential | `TroppMatrixConcentration.ch8_variational_trace_exp` | `Ch8.VariationalTraceExp` |

## Building

The project pins Lean `v4.33.1` and the Mathlib commit recorded in `lake-manifest.json`.

```
lake exe cache get
lake build
```

## License

Apache License 2.0, see [LICENSE](LICENSE).
