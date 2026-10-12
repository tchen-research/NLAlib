# Dedup round, agent F2c: generic matrix facts

Rename table: `docs/renames/2026-10-12-dedup-F2c.json` (21 entries).

## Findings executed

| Finding | Keeper (home) | Dropped | Notes |
|---|---|---|---|
| matrix_basic#23 | `trace_conjStarAlgAut`, generalised to `[CommRing R] [StarRing R]` (new `Matrix/Spectral/TraceEigenvalues.lean`) | `trace_conjStarAlgAut_complex` | proof unchanged |
| matrix_basic#20 | `trace_conjStarAlgAut`, `trace_mul_diagonal_pow_mul_mul_diagonal_pow` (TraceEigenvalues) | `SparseFock.TracePowerConvexity.{trace_conjStarAlgAut, trace_mul_diagonal_pow_mul_mul_diagonal_pow, trace_power_derivative_sum}` | in-file uses now resolve to the `NLAlib` root lemmas (`trace_power_derivative_sum` is in `Matrix/Functions/InverseCalculus`) |
| matrix_basic#21 | `trace_pow_eq_sum_eigenvalues` (moved from `Calculus/InversePowerLimit` to TraceEigenvalues) | `SparseFock.MatrixTail.trace_pow_eq_sum_eigenvalues` | MatrixTail imports TraceEigenvalues |
| matrix_basic#22 | `re_trace_pow_eq_sum_eigenvalues_pow` (moved TraceYoung → `Inequalities/TracePowers`) | `complex_re_trace_pow_eq_sum_eigenvalues` | ComplexTraceTail retargeted |
| matrix_basic#24 | the three trace lemmas above moved out of `Calculus/InversePower{Concavity,Limit}` | — | `Inequalities/TraceTail` and `Functions/CFCTrace` now import `Matrix.Spectral.TraceEigenvalues` instead of Calculus modules (CFCTrace adds `Mathlib.Analysis.Matrix.{HermitianFunctionalCalculus,Order}`) |
| matrix_basic#25, matrix_spectral#34 | `trace_eq_rank_of_isIdempotentElem`, generalised to `[Field K]` (new `Matrix/Subspaces/ProjectorTrace.lean`) | `re_trace_eq_rank_of_isIdempotentElem` | ComplexEckartYoung uses `trace_eq_rank_of_isIdempotentElem` + `Complex.natCast_re` |
| matrix_spectral#34 (pair) | `re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem`, generalised to `[RCLike 𝕜]` (ProjectorTrace) | `diag_mem_Icc_of_isSymm_of_isIdempotentElem` (ℝ) | real users (EckartYoung, Leverage) pass `Matrix.isHermitian_iff_isSymm.mpr` |
| matrix_basic#26, #27 | `finrank_ker_toBlock_eq_finrank_ker_inverse_complement`, `card_columns_sub_rank_toBlock_eq_inverse_complement`, generalised to `[Field K]` | `complex_finrank_ker_…`, `complex_card_columns_…` | atlas tag `cs-decomposition (partial)` moved onto both keepers; ComplexCSRank retargeted |
| krylov#4 | `col_mul_eq_mulVec_col`, generalised to `[NonUnitalNonAssocSemiring α]` (new `ForMathlib/LinearAlgebra/Matrix/Mul.lean`) | `col_mul` (Lanczos), `complex_col_mul_eq_mulVec_col` (ComplexBlock) | |
| krylov#5 | `transpose_mul_mul_apply_eq_dotProduct`, generalised to `[CommSemiring α]` (ForMathlib/…/Matrix/Mul) | `transpose_mul_mul_apply` (Arnoldi) | mechanical edit in F2a's Arnoldi.lean (delete + 4 uses) and ArnoldiProcess.lean (1 use) |
| krylov#22 | `inv_apply_zero_zero`, generalised to `[Field K]` (new `ForMathlib/LinearAlgebra/Matrix/Adjugate.lean`) | — (moved) | JacobiFraction imports it |
| krylov#19 | `scoped instance NLAlib.TwoPi.fact_zero_lt_two_pi` in `ForMathlib/Analysis/FourierCircle.lean` | six `local instance : Fact (0 < 2 * Real.pi)` (auto-named `instFactLtRealOfNatHMulPi_nLAlib{,_1,_2}`) | files use `open scoped NLAlib.TwoPi`; AnalyticFourier now imports FourierCircle |
| matrix_pert#34, matrix_spectral#28 | `mul_apply_self_of_isUpperTriangular`, `mul_apply_self_of_isLowerTriangular`, over `[Semiring R]` (moved Factorizations/Triangular → `ForMathlib/LinearAlgebra/Matrix/Triangular.lean`) | `mul_apply_diag_of_isLowerTriangular`, `mul_apply_self_eq_mul_of_isUpperTriangular`; also QR.lean's private copy `mul_apply_self_of_upper` | the two findings disagreed on the keeper name; kept the `mul_apply_self_of_*` pair (Factorizations naming, most uses). Users: CholeskyDefinite, CommutingSpectra, QR, Cholesky, Factorizations/Triangular |
| matrix_pert#35 | `isLowerTriangular_inv` | `isLowerTriangular_inv_of_isUnit` | CholeskyDefinite |
| (brief) | Mathlib `Matrix.BlockTriangular.mul` | `isUpperTriangular_mul`, `isLowerTriangular_mul` | LU, Cholesky, Factorizations/Triangular |
| matrix_pert#48 | `IsUpperHessenberg`, `IsTridiagonal`, `IsUnreducedHessenberg` + closure lemmas, names kept (new `Matrix/Structured/Hessenberg.lean`) | — (moved from Givens and Factorizations/Hessenberg) | Givens and QRAlgorithm import it; Factorizations/Hessenberg imports it instead of Givens. The QR-based lemmas (`isUpperHessenberg_mul_of_isQR`, …) stay in Givens. Optional Krylov restatement not done |
| matrix_pert#51 | `diag_eq_ofReal_re_of_complex_posSemidef`, `trace_eq_ofReal_re_of_complex_posSemidef`, `re_trace_nonneg_of_complex_posSemidef`, `re_trace_eq_zero_iff_of_complex_posSemidef` (new `Matrix/Basic/ComplexPosSemidefTrace.lean`) | — (moved out of Factorizations/ComplexCholeskyPivot) | GramVanishing (suggested target) belongs to F2a, so a new file. Mathlib has the `trace_nonneg` / `trace_eq_zero_iff` cores; the `Complex.re` wrappers remain |

Layer fixes:
- `Matrix/Spectral/ComplexEckartYoung` no longer imports `LowRank.Sampling.ComplexVolumeSamplingError`; it imports `Matrix.Spectral.ComplexVolumeSpectrum` and `Matrix.Subspaces.ComplexVolumeProjection`. `LowRank/Sampling/ComplexVolumeSampling` relied on the transitive import and now imports `ComplexVolumeSamplingError` directly.
- `ForMathlib/Analysis/FourierConvolution` imports `ForMathlib.Analysis.FourierCircle` and `Mathlib.MeasureTheory.Measure.Haar.Unique` instead of `Polynomial.FunctionApproximation.AnalyticApproximation`. Nothing had to move: the only NLAlib lemma it used (`fourier_apply_add`) was already in FourierCircle. `check_layers.py` no longer reports either file.

## Skipped
- matrix_pert#48 optional part (restating `ArnoldiDecomp`/`LanczosDecomp` shape facts through `IsUpperHessenberg`/`IsTridiagonal`): optional, and those files belong to other agents.

## Files created
- `NLAlib/Matrix/Spectral/TraceEigenvalues.lean`
- `NLAlib/Matrix/Subspaces/ProjectorTrace.lean`
- `NLAlib/Matrix/Structured/Hessenberg.lean`
- `NLAlib/Matrix/Basic/ComplexPosSemidefTrace.lean`
- `NLAlib/ForMathlib/LinearAlgebra/Matrix/Mul.lean`
- `NLAlib/ForMathlib/LinearAlgebra/Matrix/Adjugate.lean`

## Files deleted
- `NLAlib/Matrix/Basic/ComplexComplementaryNullities.lean`
- `NLAlib/Matrix/Basic/ComplexComplementaryRank.lean`

## For the coordinator
- `scripts/reorg.py` has no `--gen-aggregators` flag. Please regenerate aggregators: `NLAlib/Matrix/Basic.lean` still imports the two deleted files (so it fails to build), and the six new files are not in any aggregator yet (`Matrix/Spectral.lean`, `Matrix/Subspaces.lean`, `Matrix/Structured.lean`, `Matrix/Basic.lean`, `ForMathlib/LinearAlgebra/Matrix` → `ForMathlib/LinearAlgebra.lean`).
- Atlas: re-run ExtractDecls/sync_atlas. Moved tag: `cs-decomposition (partial)` now on `finrank_ker_toBlock_eq_finrank_ker_inverse_complement` and `card_columns_sub_rank_toBlock_eq_inverse_complement`.
- Edits in files owned by others (mechanical only): `Krylov/Processes/Arnoldi.lean` (deleted `transpose_mul_mul_apply`, retargeted 4 uses, added import), `Krylov/Processes/ArnoldiProcess.lean`, `Matrix/Factorizations/{LU, Cholesky, CholeskyDefinite, QR}.lean` (QR: private duplicate `mul_apply_self_of_upper` replaced by the keeper, ForMathlib import added), `LowRank/Sampling/ComplexVolumeSampling.lean` (import).
- `Krylov/Spectral/QRAlgorithm.lean` docstring (line ~33) still says the shape predicates come from Givens. Only its imports were mine to change.

## Compiled
`lake build` passed for every edited or created module and for the direct dependants of modules whose transitive imports shrank: TraceEigenvalues, TracePowers, TraceYoung, TraceMeanValue, ComplexTraceTail, TraceTail, CFCTrace, Calculus/{InversePowerConcavity, InversePowerLimit, InversePowerGrowth, GramSoftMinSpectral, UnshiftedGramSoftMin, InversePowerLaplacianLimit}, CompressionDeterminant, KyFan, Schur, NuclearHermitian, EigenspaceProjector, ProjectorTrace, EckartYoung, ComplexEckartYoung, ComplexGramTruncation, ComplexBestRankApproximation, ComplexSingularTransport, ComplexVolumeProjectorTrace, ComplexProjectionBounds, ComplementaryRank, ComplexCSRank, CSRank, JacobiBlockMinor, ForMathlib Triangular/Mul/Adjugate, Factorizations/{Triangular, LU, Cholesky, CholeskyDefinite, QR, Givens, Hessenberg, ComplexCholeskyPivot}, CommutingSpectra, Structured/Hessenberg, ComplexPosSemidefTrace, Krylov/{Block, ComplexBlock, Arnoldi, ArnoldiProcess, Lanczos, Bidiagonalization, PowerMethod, QRAlgorithm, JacobiFraction}, FourierCircle, FourierConvolution, Polynomial/{AnalyticFourier, AnalyticApproximation, JacksonPolynomial, SquareWave}, SparseFock/{MatrixTail, TracePowerConvexity, ConcreteMomentEndgame, HeavyMarkedSites, HeavyPreservingBound, LightOperators, MatrixFrameBridge, MomentTransfer}, Leverage, Nystrom/Structural, CountSketchExpectation, LowRank/{ComplexVolumeSampling, ComplexRandomPivotedCholesky, ComplexCholeskyHistories, RandomPivotedCholesky}, SLQPositiveLowerBound. No new `sorry`. `check_names.py` passes. `check_layers.py` reports only the unrelated `RademacherMgfCgf` → `HutchinsonLaws` violation.
