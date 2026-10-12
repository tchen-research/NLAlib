# Dedup round, agent P_prob (Probability)

Rename table: `docs/renames/2026-10-12-dedup-P_prob.json`. Aggregators regenerated with
`python3 scripts/reorg.py --gen-aggregators` after every file creation or deletion.
`python3 scripts/check_layers.py`: OK (the `RademacherMgfCgf → HutchinsonLaws` violation is gone).

## Block (c): the Hanson–Wright proof namespace

* `NLAlib.HansonWrightProof` no longer exists: every surviving declaration is in `NLAlib` (all 145
  original names are mapped in the rename table; there were no name clashes with NLAlib or Mathlib).
* Second matrix vocabulary retired (probability#2–#5): `deterministicOperatorNorm` → `specNorm`,
  `frobeniusNormSq` → `frobSq`, `deterministicFrobeniusNorm` → `frobNorm`,
  `matrixQuadraticForm` → `quadForm` (unfold sites use the new helper
  `quadForm_eq_sum_mul_mul` in QuadraticForms/Geometry, `zᵀAz = ∑ᵢ∑ⱼ zᵢ Aᵢⱼ zⱼ`), together with
  their API lemmas (`operatorNorm_nonneg`, `frobeniusNorm_sq`, …, see the rename table). API lemmas
  of the HW-only matrices were renamed to the canonical vocabulary (`specNorm_cutMatrix_le`,
  `frobSq_cutMatrix_le`, `frobNorm_cutMatrix_sq_le`, `sum_diag_sq_le_frobSq`,
  `abs_diag_le_specNorm`, `trace_adjoint_comp_toEuclideanCLM_eq_frobSq`).
* Duplicate endpoints deleted (probability#0, #1): `hanson_wright_inequality_hdp_explicit`,
  `hanson_wright_inequality_hdp` (`∃ c`), and with them `hansonWrightUniversalConstant{,_pos}` and the
  unused `hanson_wright_scaled_rhs_le`. `hanson_wright_inequality_hdp_explicit_constant` became the
  private `Fin n` leaf `hanson_wright_mgf_fin` of `hanson_wright_mgf` (HansonWright.lean); the private
  `hw_*` bridges are gone. Public statements of `hanson_wright_mgf` and
  `hanson_wright_of_lintegral_exp_sq_le_two` unchanged.
* Mathlib replacements (probability#9–#14): `hasSubgaussianMGF_id_map` →
  `HasSubgaussianMGF.id_map_iff`, `mgf_id_map_eq` → `mgf_id_map`, `integrable_exp_mul_id_map` →
  `integrable_map_measure`, `chernoff_bound_cgf` → `measure_ge_le_exp_cgf`, `real_inner_mul` →
  `Real.inner_apply`; `hasSubgaussianMGF_of_abs_le_of_integral_eq_zero` re-proved in 10 lines from
  Mathlib's Hoeffding lemma `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`; `exp_le_chord` deleted.
* Scalar sub-Gaussian block moved to layer-1 files (probability#6, #7, #8), three files because of
  size: `Probability/SubGaussian/EvenMoments.lean` (mean, Hoeffding, even moments, Taylor terms),
  `Probability/SubGaussian/ExpSquare.lean` (exp-square series and bounds, integrability),
  `Probability/SubGaussian/CenteredSquare.lean` (centred-square MGF/CGF, products of independent
  variables, `cgf_const_mul`, `iIndepFun_centered_sq` generalised from `Fin n` to any index type).
  The five former `alias`es of SubGaussian/Moments are now the theorems themselves
  (`hasSubgaussianMGF_mono`, `integral_eq_zero_of_hasSubgaussianMGF`,
  `integral_pow_two_mul_le_of_hasSubgaussianMGF`, `integral_exp_mul_sq_le_of_hasSubgaussianMGF`,
  `hasSubgaussianMGF_finset_sum_mul_of_iIndepFun`); Moments imports ExpSquare, not the HW chain.
  STANDARDS renames: `mean_le_log_mgf` → `integral_le_one_div_mul_log_integral_exp_mul`,
  `hasSubgaussianMGF_integral_le_zero` → `integral_nonpos_of_hasSubgaussianMGF`,
  `integral_fourth_le_…` → `integral_pow_four_le_…`.
* Real/measure-theory helpers to new ForMathlib files (probability#21, #22):
  `ForMathlib/Analysis/ExpBounds.lean` (`exp_mul_sq_eq_tsum`, `factorial_two_mul_div_factorial_le_succ_pow`,
  `cosh_taylor_term_le`, `exp_neg_le_one_sub_add_sq`, `exp_neg_mul_one_add_le_one`,
  `exp_add_le_average_exp_two`, and `exp_le_one_add_add_sq_mul_exp_abs` from OrliczMGF),
  `ForMathlib/MeasureTheory/MapProd.lean` (`measure_map_prod_map_of_aemeasurable`),
  `ForMathlib/Probability/IndepExpSum.lean` (`iIndepFun.integrable_exp_mul_sum₀`). New files because
  existing ForMathlib files were reference-only for this round.
* probability#27: the HW local-CGF Chernoff pair moved to Scalar/ScalarBernstein as
  `measureReal_ge_le_exp_of_cgf_le` and `measureReal_abs_ge_le_two_mul_exp_of_cgf_le` (stated with
  `μ.real`); the Bernstein-specific `measureReal_{,abs_}ge_le_bernstein_of_local_mgf` are deleted and
  `bernstein_sum_of_lintegral_exp_abs_le_two` is derived from the general two-sided bound
  (`C = 16`, `b = B/16`).
* Chain files: ScalarMoments, ExponentialSeries, CenteredSquareBounds deleted (their matrix
  remainders merged into GaussianProductIntegrability). `scripts/AuditNewProofs.lean` module list
  updated.
* Not done: the remaining `Source-transport helper …` docstrings of the HW chain still do not say
  what each lemma states (pre-existing; ~90 lemmas). `quadForm_eq_sum_mul_mul`,
  `abs_diag_le_specNorm`, `sum_diag_sq_le_frobSq` are deterministic and should move to
  Matrix/Basic/QuadForm and Matrix/Norms (owners: P_basic / P_norms).

## Block (a): `LoewnerLE` retired

* Every statement and proof now uses Mathlib's `≤` (`open scoped MatrixOrder`, `Matrix.le_iff`);
  `unfold LoewnerLE` → `rw [Matrix.le_iff]`. Definition deleted from Matrix/Functions/ExpLog. No
  `abbrev` fallback was needed. Files touched: TraceExpMonotone, OperatorTheory/{Basic,
  EntropyJointConvex, JensenIsometricCompression, OperatorJensen, PerspectiveConvex} (reference
  edits) and 11 Concentration/Matrix files. STANDARDS §3 vocabulary now names the Loewner order;
  docs/TroppMatrixConcentration.md updated. The only atlas tag on the def (`matrix-calculus-def`) is
  carried by the other ExpLog definitions. No bridge lemma: `Matrix.le_iff` is the bridge.

## Block (b): `spectralNorm` retired

* `spectralNorm A` → `‖A‖` (L2 operator norm) in all 21 files (specNorm is still ℝ-only, so the
  minimal option was taken); definition deleted from ExpLog. Renamed: 
  `lambdaMin_le_or_le_lambdaMax_of_le_spectralNorm_sub_one` → `…_of_le_norm_sub_one`,
  `measure_spectralNorm_uniform_{iid,subset}_sub_one_le` → `measure_norm_uniform_…`.
  Left for owners: `specNorm_le_spectralNorm_map_ofReal` (Matrix/Norms/RealComplexNorm, P_norms) and
  `measure_le_spectralNorm_leverage_gram_sub_one` (Sketching) still carry the old word in their names.

## Block (d): scalar laws

* `IsStandardGaussian` and its API (`aemeasurable_of_isStandardGaussian`,
  `memLp_two_and_moments_of_isStandardGaussian` (was `standardGaussian_hutchinson_moments`),
  `hasSubgaussianMGF_of_isStandardGaussian` (from Estimation/Trace/HutchinsonTail),
  `hasSubgaussianMGF_id_gaussianReal` (from RandomMatrix/…/LinearImage),
  `integrable_pow_gaussianReal`, `integral_pow_three_gaussianReal`, `integral_pow_four_gaussianReal`
  (from FourthMoment)) now live in the new `Probability/Gaussian/Basic/StandardGaussian.lean`.
* `IsRademacher μ r := μ.map r = rademacherMeasure` (no longer a copy of the measure) with
  `aemeasurable_of_isRademacher`, `memLp_two_and_moments_of_isRademacher` in Probability/Rademacher/Core
  (which no longer imports ScalarLaws). ScalarLaws keeps `gaussianSeriesTail` and imports both leaves.
* `integrable_and_integral_quadForm_eq_trace_of_second_moments` moved to QuadraticForms/QuadraticMoments
  and `integral_quadForm_eq_trace` is its corollary (probability#18).
* Reference edits: Estimation/{HutchinsonLaws, HutchinsonTail, DiagonalEstimator, SLQRademacher}.
* RademacherMgfCgf imports Rademacher/Core instead of Estimation/HutchinsonLaws (probability#37).
* `integrable_sq_gaussianReal` deleted for `integrable_pow_gaussianReal 2` (probability#46).
* Not done: `rademacher_pi_coordinate_moments` was not re-derived from the moments lemma (optional).

## Block (e): matrix concentration (done by P_prob)

* New layer-0 files (names unchanged, only imports moved):
  `Matrix/Functions/HermitianCalculus.lean` (deterministic part of Concentration/Basic/MatrixCalculus,
  which keeps `integral_reindex`, `integral_fromBlocks_diag`),
  `Matrix/Functions/UnitaryCalculus.lean` (whole file, plus `posDef_reindex_iff`,
  `matrixLog_reindex_of_isHermitian` from LiebReindex),
  `Matrix/Functions/TraceExpBounds.lean` (whole file, plus `traceExp_nonneg_of_isHermitian`,
  `traceExp_smul_one_eq_card_mul_exp` from TraceIntegrability and
  `exp_mul_lambdaMax_lambdaMin_le_traceExp_smul` from TailSpectralComparison, **generalised to any
  nonempty finite index type**), `Matrix/Functions/DilationIdentities.lean`,
  `Matrix/OperatorTheory/GoldenThompson.lean` (the two `Fin` steps made private, probability#34),
  `Matrix/OperatorTheory/LiebTraceFunction.lean` (`continuousOn_traceExp_add_matrixLog`
  **generalised to any finite index type**, `lieb_concavity_finite`). Deleted Probability files:
  UnitaryCalculus, LiebReindex, TraceExpBounds, TailSpectralComparison, GoldenThompson,
  DilationIdentities.
* `_finite` copies deleted: `continuousOn_traceExp_add_matrixLog_finite`,
  `exp_mul_lambdaMax_le_traceExp_smul_finite`; `traceExp_smul_one` → keeper (probability#31–#33).
  `traceExp_le_traceExp_finite` and `posDef_…_finite` had already been removed by P_pert.
  `lieb_concavity_finite` stays (in LiebTraceFunction) until P_pert generalises `lieb_concavity`.
* Private helper copies promoted (probability#35): `traceFunction_eq_sum` (×4; public in
  Concentration/Basic/IntrinsicDimension, any finite index), `traceExp_pos` (×3) →
  `traceExp_pos_of_isHermitian`, `traceExp_le` (×2) → `traceExp_smul_le_mul_exp_mul_norm`,
  `matrix_exp_sum_norm_bound` (×2) → `norm_matrixExp_sum_le_prod` (all in TraceExpBounds);
  `proj`/`cfc_eq_sum`/`smul_sq_eq`/`matrixExp_smul_sq_eq` (×2) → `eigenProj`,
  `cfc_eq_sum_smul_eigenProj`, `smul_sq_eq_cfc`, `matrixExp_smul_sq_eq_cfc` (HermitianCalculus, any
  finite index), `integral_eq` (×2) → `integrable_and_integral_matrixExp_smul_eq_cfc_mgf`
  (MatrixCalculus).
* ForMathlib (probability#20, #38, #39): new `ForMathlib/Analysis/SpecialFunctions/Gamma.lean`
  (`Gamma_add_half_le_mul_sqrt`, `lintegral_ofReal_mul_rpow_mul_exp_Ioi`, `lintegral_rpow_mul_exp_le`),
  `ForMathlib/Analysis/Convex/Integral.lean` (`ConcaveOn.le_map_integral_of_integral_mem`),
  `ForMathlib/MeasureTheory/IntegralUpdate.lean` (`measurable_integral_update_pi`); the two log
  inequalities of Sampling added to ExpBounds.
* probability#26: McDiarmid's `integrable_exp_mul_of_abs_le` replaced by Mathlib
  `integrable_exp_mul_of_mem_Icc`.
* probability#45: `integral_mul_eq_integral_deriv_gaussianReal_of_integrable` moved into
  IntegrationByParts; the bounded version is now its corollary; the private
  `hasDerivAt_gaussianPDFReal_zero_one` and `gaussianPDFReal_zero_one_eq` are gone.

## Block (g), specific Mathlib imports (sub-agent C)

Finding probability#23 (STANDARDS §2). `import Mathlib.Tactic` removed from all 14 assigned files;
in every case the tactics used were already available through the file's other imports, so **no
replacement imports were needed** and no proof or declaration changed.

- Converted (import line deleted, nothing added): `Probability/Concentration/QuadraticForms/`
  `Geometry`, `CutAverages`, `GaussianProductIntegrability`, `DiagonalCGF`, `Centering`,
  `LinearFormComparison`, `VectorProductComparison`, `Decoupling`, `TailAssembly`, `UniversalBound`;
  `Probability/Concentration/Entropy/EntropyTensorizationNonneg`;
  `Probability/Gaussian/Concentration/LogSobolevCoverage`;
  `Probability/Gaussian/Calculus/OrnsteinUhlenbeckGrowth`, `OrnsteinUhlenbeckEntropyGrowth`.
- Left with `Mathlib.Tactic`: none of the assigned files. (`Gaussian/Basic/GaussianMatrix`,
  `Gaussian/Moments/FourthMoment`, `Gaussian/Concentration/LipschitzConcentration` were out of scope
  by instruction and not touched.)
- Dependants edited: none. Checked by building the full non-aggregator reverse-import closure of the
  14 modules (27 modules, incl. `QuadraticForms.HansonWright`, `SquaredProjections`,
  `Gaussian.Concentration.LogSobolevHerbst`, `RandomMatrix.SubGaussian.{SubGaussianJL,SubGaussianRows}`,
  `Estimation.Trace.{HutchinsonTail,Unbiased}`, `Estimation.Quadrature.SLQ*`): green.

## Block (e), Gaussian/** (sub-agent A)

Findings probability#42, #43, #44, #48: all executed, none skipped. Every touched module and its
full non-aggregator reverse-import closure builds green (`lake build <modules>`), no warnings.

- **probability#43** (polar coordinates). Keeper `integral_radial_pi_gaussianReal`
  (`Gaussian/Moments/PositiveMoments`). `ExpectationNormDiff` now imports `PositiveMoments` and
  `ForMathlib/Analysis/SpecialFunctions/Gamma`; deleted its private copies `en_pi_gauss`,
  `en_prod_pdf`, `en_sum_sq_ofLp`, `en_radial`. `PositiveMoments`' private
  `integral_rpow_mul_exp_neg_sq_div_two` (`∫₀^∞ yˢ e^{-y²/2} = 2^{(s+1)/2}·½·Γ((s+1)/2)`) is now
  public with a docstring (`atlas: gaussian-positive-moments`); `enJ_eq` is a two-line wrapper of
  it, `enJ_rec` adapted to the `2^{…}` form, and `enJ_logconvex` now uses
  `NLAlib.Gamma_add_half_le_mul_sqrt` instead of re-deriving the Bohr–Mollerup step (~20 lines
  shorter). No public name dropped.
- **probability#42** (rotation interpolation). Keeper `integral_le_integral_of_covariance_hessian_nonneg`
  moved verbatim (with `atlas: gordon-minimax`) from `Comparison/GordonMinimax` into
  `Comparison/Interpolation` (which now imports `Gaussian/Calculus/IntegrationByParts`). The private
  `sl_compare` (Slepian) is re-proved from it with `X, Y` swapped (Gaussian law swapped by
  `map_fun (snd.prod fst)`, `C + C²` as common bound, `K = 1`, sign condition from `hvar`/`hinc`,
  ~40 lines instead of ~175); `sf_softmax_compare` (SudakovFernique) re-proved from it (`C = 1 + 2β`,
  `K = log|ι|/β`, sign via `sf_quad_nonneg`; ~30 lines instead of ~175). Hypotheses matched
  exactly; nothing kept. Redundant `IntegrationByParts` imports dropped from Slepian,
  SudakovFernique, GordonMinimax. No public name dropped.
- **probability#44** (Herbst). `gaussian_concentration_pi` re-proved in 8 lines from
  `integrable_of_logSobolev_of_lipschitz` and `measure_ge_le_of_logSobolev` with
  `hasEuclideanLogSobolev_pi_gaussianReal` at threshold `L t`. Statements of
  `gaussian_concentration_pi` and `gaussian_concentration` unchanged. Import cycle avoided:
  `LogSobolevHerbst` previously imported `LipschitzConcentration` only for the deterministic helpers,
  which moved verbatim to the NEW `ForMathlib/Analysis/LipschitzApprox.lean`
  (`continuous_of_abs_sub_le_mul_sqrt_sum_sq`, `sum_sq_fderiv_le_sq_of_lipschitz`,
  `exists_contDiff_abs_sub_le_of_lipschitz`, private `sqrt_sum_sq_sub_le_card_mul_dist`);
  `LogSobolevHerbst` now imports `LipschitzApprox` + `Probability/Concentration/Entropy/Herbst`, and
  `LipschitzConcentration` imports `LogSobolevHerbst`. Dropped (public): `entropy_exp_mul_le_gaussian_of_lipschitz`
  (its `atlas: herbst` tag is already on the keeper `measure_ge_le_of_logSobolev`),
  `integrable_exp_mul_gaussian_of_lipschitz`, `integrable_gaussian_of_lipschitz`,
  `integrable_exp_mul_sum_abs_gaussian`, `integrable_exp_mul_abs_gaussianReal`; dropped (private):
  `abs_sub_le_abs_mul_sqrt_sum_sq`, `integrable_mul_exp_of_abs_sub_le`,
  `entropy_exp_mul_le_of_contDiff`. LipschitzConcentration: 484 → ~95 lines.
- **probability#48** (misplaced helpers), names unchanged. `measure_ge_le_of_measure_gt_le` (with its
  private helpers `approachingThreshold*`, `ge_tail_eq_iInter`, `strict_tail_antitone`) moved from
  `Comparison/SlepianTails` to the NEW `ForMathlib/MeasureTheory/TailComparison.lean`.
  `pi_gaussianReal_map_dotProduct_unit` (from `RandomMatrix/Gaussian/InverseMoments/Probe`) and
  `integrable_and_integral_dotProduct_sq_pi_gaussianReal` (from `…/InverseMoments/OffDiagonal`) moved
  to the NEW `Probability/Gaussian/Basic/StandardVector.lean`; Probe and OffDiagonal import it
  (OffDiagonal's module-docstring bullet removed).

Files created: `NLAlib/ForMathlib/Analysis/LipschitzApprox.lean`,
`NLAlib/ForMathlib/MeasureTheory/TailComparison.lean`,
`NLAlib/Probability/Gaussian/Basic/StandardVector.lean`. Deleted: none. Aggregators regenerated
(`scripts/reorg.py --gen-aggregators`); `check_layers.py` OK.
Files edited: `Gaussian/Moments/{PositiveMoments,ExpectationNormDiff}`,
`Gaussian/Comparison/{Interpolation,GordonMinimax,Slepian,SudakovFernique,SlepianTails}`,
`Gaussian/Concentration/{LipschitzConcentration,LogSobolevHerbst}`,
`RandomMatrix/Gaussian/InverseMoments/{Probe,OffDiagonal}` (cut + import only).

Coordinator: the atlas Lean side lists `NLAlib.entropy_exp_mul_le_gaussian_of_lipschitz` (atlas
`herbst`) and module paths for the moved declarations; regenerate from tags. Rename entries added to
`docs/renames/2026-10-12-dedup-P_prob.json`. `gaussian_concentration` still lives in
`LipschitzConcentration` (P_prob moves it).

## Block (f): `gaussianMatrix` to the random-matrix layer (P_prob)

* New `RandomMatrix/Gaussian/Basic/GaussianMatrix.lean`: `gaussianMatrix` and its whole API (names
  unchanged), plus `linForm`, `linForm_eq_frobInner`, `continuous_linForm` moved next to it from
  `RandomMatrix/Gaussian/Basic/LinearForms.lean` (randnla#19, first half). The matrix-free
  `hasGaussianLaw_id_pi_gaussianReal` stays in Probability, now in
  `Probability/Gaussian/Basic/StandardVector.lean` (ProductIntegrationByParts imports that instead).
  `Probability/Gaussian/Basic/GaussianMatrix.lean` deleted.
* FourthMoment (the entry/linear-form Wick lemmas and `integral_frobSq_mul_gaussianMatrix_mul_sq`,
  i.e. its whole matrix half; its scalar moments had already moved to StandardGaussian in block (d))
  moved to `RandomMatrix/Gaussian/Moments/FourthMoment.lean`, next to SecondMoment (randnla#25);
  `Probability/Gaussian/Moments/FourthMoment.lean` deleted.
* `gaussian_concentration` (Gaussian-matrix form, with its private `frobNorm_curry_sub`) moved to the
  new `RandomMatrix/Gaussian/Basic/LipschitzConcentration.lean`; `gaussian_concentration_pi` stays in
  Probability. Spectral/Deviation imports the new file.
* Import rewrites (mechanical): RandomMatrix/Gaussian/{Basic/Lipschitz, Invariance/Invariance,
  Moments/SecondMoment, Moments/ApproxMultiplication, Spectral/Deviation},
  Estimation/QuadraticForms/HutchinsonLaws. No Probability file uses `gaussianMatrix` any more.
* The 77-module reverse-import closure builds green; `check_layers.py` OK.
* Left for P_randnla (randnla#19 second half): restating
  `integral/integrable_linear_mul_{two,four}_gaussianMatrix` with `linForm` and deriving
  `integral_linForm_sq_gaussianMatrix` as the `u = v` corollary; both now sit in RandomMatrix files.

## Block (e), matrix concentration leftovers (sub-agent B)

Executed (probability#35, private helper copies in Concentration/Matrix):
* `norm_compress_le` (DilationVariance, BlockIntrinsic; identical) → public
  `norm_conjTranspose_mul_mul_le` (`Eᴴ E = 1 → ‖Eᴴ M E‖ ≤ ‖M‖`), and `norm_fromBlocks_diag`
  (same statement in both files, bodies differed only in line breaks) → public `norm_fromBlocks_diag`;
  both **generalised from ℂ to any `RCLike 𝕜`**, any finite index types. New section `BlockDiagonal`
  of `Matrix/Functions/HermitianCalculus.lean`.
* `posSemidef_fromBlocks_diag` (BlockIntrinsic, IntrinsicBernsteinExpectation; identical) → public
  `posSemidef_fromBlocks_diag` in the same section, **generalised to any `StarOrderedRing`** (covers ℝ
  and ℂ). Follow-up for the owner of `Matrix/Inequalities/BlockOrderConsequences.lean`: its real
  `fromBlocks_zero_posSemidef` is now a special case and could be dropped in favour of this keeper.
* `trace_re_nonneg` (BlockIntrinsic, IntrinsicHermitianBernstein): Mathlib composition
  `(Complex.nonneg_iff.mp hA.trace_nonneg).1`; both private copies deleted and the term inlined at the
  three uses. No public lemma added.
* `norm_exp_le` ×4 left alone, as instructed.

Executed (probability#36, rest of the deterministic block; names unchanged, only imports move):
* New `Matrix/Functions/ExtremeEigenvalues.lean`: `lambdaMax_smul_of_pos`, `lambdaMin_smul_of_pos`,
  `lambdaMax_one`, `lambdaMin_one` (from Sampling's spectral section) and all of
  SamplingSpectralBounds (`lambdaMin_nonneg_of_posSemidef`, `lambdaMax_le_trace_of_posSemidef`,
  `lambdaMin_le_or_le_lambdaMax_of_le_norm_sub_one`; verified deterministic). Deleted
  `Probability/Concentration/Matrix/SamplingSpectralBounds.lean`.
* New `Matrix/Functions/IntrinsicDimension.lean`: merge of the three wholly deterministic files
  `Concentration/Basic/IntrinsicDimension` (`intrinsicDimension`, `traceFunction`,
  `traceFunction_eq_sum`), `Concentration/Matrix/IntrinsicDimension`
  (`traceFunction_le_intrinsicDimension_mul`) and `Concentration/Matrix/BlockIntrinsic`
  (`intrinsicDimension_fromBlocks`). All three deleted; atlas tags kept on the moved docstrings.
* `Matrix/Functions/TraceExpBounds.lean` gains `continuous_traceExp` (from TraceIntegrability),
  `exp_sub_le_traceExp_compensated_of_crossing` (all of Martingales/TracePotentialCrossing, file
  deleted) and `convexOn_traceExp_smul_selfAdjoint` (from SamplingWithoutReplacement).
* `Matrix/Functions/HermitianCalculus.lean` gains BernsteinMgfCgf's matrix bounds
  `one_add_smul_add_smul_sq_eq_cfc`, `matrixExp_smul_le_one_add_smul_add_smul_sq_of_spectrum_le`,
  `one_add_le_matrixExp_of_isHermitian`.
* `ForMathlib/Analysis/ExpBounds.lean` gains `exp_mul_le_one_add_mul_add_sq_mul_of_le` with its
  private `gFun`/`hFun` scaffolding.
* Importers fixed: Sampling, SamplingWithoutReplacement(+Tails), UniformIidSampling, TraceIntegrability,
  BernsteinMgfCgf, FreedmanGlobal, GeneralizedLaplace, IntrinsicChernoff, IntrinsicHermitianBernstein,
  IntrinsicBernstein, DilationVariance, IntrinsicBernsteinExpectation; foreign mechanical edits:
  `Sketching/Sampling/LeverageSampling.lean` (import SamplingSpectralBounds → Sampling: it also
  uses `matrix_chernoff_sampling`, so it keeps a probability import) and the module list of
  `scripts/AuditNewProofs.lean`.
* Left in Probability on purpose (deterministic but not matrix analysis): the named tail
  expressions `chernoffCgfCoefficient`, `chernoffLowerTail`, `chernoffUpperTail`, `bernsteinTail`,
  `gaussianSeriesTail`, `mcdiarmidTail` (vocabulary of the probabilistic statements), and
  `matrixVectorSqNorm`/`matrixQuadraticFormReal` (interface of `HasLocalMatrixSecondMoment`;
  `matrixQuadraticFormReal` is a second spelling of a quadratic form, worth a look by the owner of
  `quadForm`). **Follow-up:** the ε-net lemmas of `Concentration/Basic/Net.lean`
  (`specNorm_le_div_of_net*`, `exists_finset_sphere_net`, …; 9 of 11 declarations deterministic)
  belong in `Matrix/Norms` (not a directory this agent may create files in).
* Private deterministic duplicates noticed but not in the task: IntrinsicChernoff's private
  `lambdaMin_nonneg` (Fin) and IntrinsicBernsteinExpectation's `norm_le_trace` duplicate
  `lambdaMin_nonneg_of_posSemidef` / `lambdaMax_le_trace_of_posSemidef`; IntrinsicHermitianBernstein's
  `lambdaMax_zero`.

Skipped:
* Task 3 (JensenIsometricCompression, P_pert's file): not a mechanical substitution. The private
  `reindexStar` is a `≃⋆ₐ[ℝ]` equivalence (needed for `StarAlgHomClass.map_cfc` with the real
  calculus) while the public `reindexStarAlgEquiv` is `≃⋆ₐ[ℂ]`, and there is no public
  `cfc`-reindex lemma replacing `reindex_cfc`. The private `unitary_calculus` (self-adjoint
  involution `U`, `U * A * U`, conjunction of three facts) has no public twin: `cfc_unitary_conj`
  takes `U : unitary` and `U * A * Uᴴ`, so every use would need a proof rewrite. Importing
  UnitaryCalculus there would not create a cycle.
* Task 4: `lieb_concavity` (Matrix/OperatorTheory/LiebConcavity.lean) is still stated over `Fin d`;
  `lieb_concavity_finite` stays.

Files created: `Matrix/Functions/ExtremeEigenvalues.lean`, `Matrix/Functions/IntrinsicDimension.lean`.
Files deleted: `Probability/Concentration/Matrix/{SamplingSpectralBounds,IntrinsicDimension,BlockIntrinsic}.lean`,
`Probability/Concentration/Basic/IntrinsicDimension.lean`,
`Probability/Concentration/Martingales/TracePotentialCrossing.lean`. Aggregators regenerated
(`scripts/reorg.py --gen-aggregators`). No public name was dropped or renamed (rename table
unchanged). Built: all touched modules, their reverse-import closure (100 modules) and the
affected aggregators.

## Final state and notes for the coordinator (P_prob)

* Final check: `lake build NLAlib.Probability NLAlib.Matrix.Functions NLAlib.Matrix.OperatorTheory
  NLAlib.ForMathlib NLAlib.RandomMatrix NLAlib.Estimation NLAlib.Sketching` (4514 jobs) is green;
  `check_layers.py` OK; `check_names.py` OK; no dangling `import NLAlib.*`; aggregators regenerated.
* Block (g): no `import Mathlib.Tactic` is left in Probability or in the files created this round.
* Atlas: regenerate the Lean side from the tags (many modules moved; dropped declarations are listed
  in the rename table, e.g. `NLAlib.entropy_exp_mul_le_gaussian_of_lipschitz`, `NLAlib.LoewnerLE`,
  `NLAlib.spectralNorm`). `atlas/atlas.json` was not edited.
* Follow-ups for other owners: P_pert: generalise `lieb_concavity` to finite types (then delete
  `lieb_concavity_finite` in Matrix/OperatorTheory/LiebTraceFunction), and the
  JensenIsometricCompression private copies need a real proof rewrite (`reindexStar` is `≃⋆ₐ[ℝ]`).
  P_norms: rename `specNorm_le_spectralNorm_map_ofReal`; host the deterministic ε-net lemmas of
  Concentration/Basic/Net in Matrix/Norms; move `abs_diag_le_specNorm`, `sum_diag_sq_le_frobSq`
  (QuadraticForms/CutAverages). P_basic: move `quadForm_eq_sum_mul_mul` (QuadraticForms/Geometry) to
  Matrix/Basic/QuadForm; `matrixQuadraticFormReal` (Martingales/LocalSecondMoment) is a second
  spelling of `quadForm`. P_randnla: randnla#19 second half (restate the FourthMoment linear-form
  lemmas with `linForm`), and `measure_le_spectralNorm_leverage_gram_sub_one` still has the old word
  in its name. Inequalities owner: `fromBlocks_zero_posSemidef` is subsumed by
  `posSemidef_fromBlocks_diag`.
* Skipped: probability#41 (Net to Matrix/Norms: not a directory P_prob may create files in);
  `norm_exp_le` ×4 (signatures differ); `rademacher_pi_coordinate_moments` re-derivation (optional);
  ChiSquare `Fin d` vs `Fintype` keeper (left to the coordinator by the review).
