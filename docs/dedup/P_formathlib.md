# Dedup round, agent P_formathlib: ForMathlib

Rename table: `docs/renames/2026-10-12-dedup-P_formathlib.json` (6 entries).

## Findings executed

| Finding | Keeper | Dropped / moved | Files touched |
|---|---|---|---|
| formathlib#0 | Mathlib `InnerProductSpace.gramSchmidt_def''` | `gramSchmidt_eq_sub_sum_inner_div_norm_sq` (deleted) | `ForMathlib/Analysis/InnerProductSpace/GramSchmidt.lean` (4 in-file uses now `eq_sub_of_add_eq (gramSchmidt_def'' ℝ f j).symm` or `gramSchmidt_def''` directly) |
| formathlib#1 | Mathlib `Polynomial.degree_smul_le` (+ `C_mul'`) | `degree_C_mul_le` (deleted) | `ForMathlib/Algebra/Polynomial.lean`; `Polynomial/BestApproximation/Minimax.lean` (3 uses → `(congrArg degree (C_mul' _ _)).trans_le (degree_smul_le _ _)`) |
| formathlib#4 | `charpoly_eq_mul_of_isolated_equiv` | `charpoly_eq_X_sub_C_mul_submatrix_of_isolated_coordinate`: name kept, moved from `Matrix/Spectral/EigenvectorDeflationSpectrum.lean` to `ForMathlib/LinearAlgebra/IsolatedCharpoly.lean`, generalised `Field` → `CommRing`, and reproved in 6 lines as the special case `e := Fin 1 ⊕ {j // j ≠ i} ≃ n` of the keeper (the 40-line block-matrix proof is gone) | EigenvectorDeflationSpectrum now imports IsolatedCharpoly (no other edit; its single use is unchanged) |
| formathlib#5 | `ExactRowSubset` | `SizedSubset k r` is now `abbrev … := ExactRowSubset k (Fintype.card r)` (definitionally equal to the old body) | new `ForMathlib/Data/ExactRowSubset.lean` holds `ExactRowSubset` and `exactRowSubset_nonempty` (cut from `ForMathlib/Probability/UniformSamplingCoupling.lean`, which imports it); `ExactRowSubset` lost its unused `[Fintype α]` argument so that `SizedSubset` (no `Fintype k`) can use it; `Matrix/Basic/CauchyBinet.lean` imports the small file instead of a probability file |
| formathlib#9 | `ForMathlib/Analysis/FourierCircle.lean` | `fourier_apply_neg`, `fourier_nat_eq_pow`, `fourier_one_eq_circleMap` moved verbatim from `Polynomial/FunctionApproximation/AnalyticFourier.lean` (names kept) | FourierCircle adds `import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap`; module docstring updated |
| formathlib#19–22 (unused) | — | `hasDerivAt_integral_sub_kernel`, `antitoneOn_integral_sub_of_integral_deriv_nonneg` (MonotoneDensity), `integrable_pi_of_coordinate_oscillation` (BoundedDifferences), `prod_sub_erase_ne_zero_of_injective` (InterlacingWeights) deleted; no atlas tags; module docstrings of MonotoneDensity and BoundedDifferences updated | |
| review "near-Mathlib wrappers" | — | kept; module docstrings now carry an "Upstreaming note" naming the Mathlib lemma: GramSchmidt (`inner_gramSchmidtNormed_eq_zero_of_lt` ← `gramSchmidt_inv_triangular`), FourierCircle (`fourier_apply_add`, `fourier_apply_neg`, `fourier_nat_eq_pow` ← `fourier_apply`/`fourier_add`), FourierConvolution (`integral_haarAddCircle_eq_inv_mul_intervalIntegral` ← `AddCircle.integral_haarAddCircle` + `AddCircle.intervalIntegral_preimage`; `fourier_apply_sub`), InterlacingInterpolation (`degree_sub_lt_of_monic_natDegree_eq` ← `Polynomial.degree_sub_lt_left`), NonnegativeSupermartingale (`integral_stoppedValue_le_integral_zero_of_supermartingale` ← `Submartingale.expected_stoppedValue_mono` on `-S`), BoundedDifferences (`hasSubgaussianMGF_of_range_oscillation` ← `hasSubgaussianMGF_of_mem_Icc`), Matrix/Order (`matrix_smul_le_smul_of_nonneg`, `re_trace_le_re_trace_of_le` ← `Matrix.PosSemidef.smul` / `trace_nonneg`) | |

## Already done in phase 1 (F2c), verified, nothing to do
- formathlib#2 (`isLowerTriangular_inv_of_isUnit` deleted, CholeskyDefinite uses `isLowerTriangular_inv`).
- formathlib#3: F2c kept the `mul_apply_self_of_isLowerTriangular` name (in ForMathlib, over `Semiring`) and dropped `mul_apply_diag_of_isLowerTriangular`, the reverse of this finding's naming; the duplicate is gone.
- formathlib#8 (FourierConvolution import).

## Skipped
- formathlib#6, #7 (move FiniteLaw / FiniteL2 to Sketching/Sparse) and the FiniteLaw/FiniteL2 unused or simp-only declarations #11–#18, #23–#25 (`WeightedONBasis.{vacuum_moment, vacuum_mulOp, mulOp_pow, mulOp_one}`, `FiniteLaw.{abs_expect_le_expect_abs, expect_neg, prob_mem_Icc, toMeasure_singleton, expect_zero, prob_empty, prob_univ}`): per instructions, those files are left untouched for the sparse-sketch integration round (docs/SPARSE_INTEGRATION.md), which moves them into Sketching/Sparse; that round should decide the 8 unused ones there.
- formathlib#10 (`ConcaveOn.le_map_integral_of_integral_mem` out of LiebJensen): owned by P_prob (its finding probability#38, target `ForMathlib/Analysis/Convex/Integral.lean`); not yet moved when I checked, left to P_prob.
- formathlib#26–28 (`finOneSumSuccAboveEquiv_inr`, `matrixQuadraticFormCLM_apply`, `matrixRealQuadraticFormCLM_apply`): `@[simp]` API, kept (not tested by deletion).
- formathlib#5 optional rename `ExactRowSubset` → `FinsetOfCard`: not done (9 files across Probability/Sketching owned by other agents, plus derived names such as `uniformExactRowSubsetPMF`); a follow-up if wanted.

## Files created / deleted
- Created `NLAlib/ForMathlib/Data/ExactRowSubset.lean`. Ran `python3 scripts/reorg.py --gen-aggregators` (93 aggregators regenerated).

## For the coordinator
- Atlas: no tags moved (none of the dropped declarations carried one). Re-run ExtractDecls/sync for the moved declarations (`charpoly_eq_X_sub_C_mul_submatrix_of_isolated_coordinate`, three Fourier lemmas, `ExactRowSubset`, `exactRowSubset_nonempty`).
- Mechanical edits in foreign files: `Polynomial/BestApproximation/Minimax.lean` (3 uses), `Polynomial/FunctionApproximation/AnalyticFourier.lean` (three lemmas cut), `Matrix/Spectral/EigenvectorDeflationSpectrum.lean` (lemma cut, import added), `Matrix/Basic/CauchyBinet.lean` (`SizedSubset` body and import).
- Noticed, not in scope: `ForMathlib/Algebra/InterlacingWeights.lean` imports `Mathlib.Tactic` (STANDARDS §2 wants specific imports).

## Compiled
`lake build` passed for: ForMathlib GramSchmidt, Algebra/Polynomial, FourierCircle, FourierConvolution, IsolatedCharpoly, Data/ExactRowSubset, Data (aggregator), UniformSampling{Coupling,Counts,Marginals,Jensen}, MonotoneDensity, WeakDensity, LocalWeakDensity, WeightedWeakDensity, BoundedDifferences, InterlacingWeights, InterlacingInterpolation, NonnegativeSupermartingale, Analysis/Matrix/Order; Polynomial Minimax, Lagrange, AnalyticFourier, AnalyticApproximation, JacksonPolynomial, Jackson, SquareWave, AnalyticInterpolation; Krylov AnalyticQuadrature; Matrix CauchyBinet, CauchyBinetAdjoint, EigenvectorDeflationSpectrum, EigenvectorDeflationBlocks, GershgorinBounds, InterlacingRestoration, InterlacingInduction, InterlacingStrictConstruction, SimpleEigenvaluePerturbation; Probability SamplingWithoutReplacement{,Tails}, McDiarmid; Sketching SRHTCore, SRHT. No `sorry` added. `check_names.py` passes; `check_layers.py` reports only the unrelated `RademacherMgfCgf` → `HutchinsonLaws` violation (P_prob's).

## Summary
6 declarations deleted (2 Mathlib restatements, 4 unused), 6 moved into ForMathlib with their names kept (3 Fourier lemmas, `charpoly_eq_X_sub_C_mul_submatrix_of_isolated_coordinate` reproved from the keeper, `ExactRowSubset`, `exactRowSubset_nonempty`), 1 definition re-expressed (`SizedSubset`). Kept: 3 `@[simp]` lemmas plus the FiniteLaw/FiniteL2 family (14 findings deferred to the sparse integration round); about 10 near-Mathlib wrappers kept and documented as upstreaming candidates.
