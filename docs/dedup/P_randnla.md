# Dedup round, agent P_randnla (RandomMatrix, LowRank, Sketching except Sparse)

Rename table: `docs/renames/2026-10-12-dedup-P_randnla.json` (33 entries).

## Findings executed

| finding | keeper (home) | dropped / moved | notes, files touched |
|---|---|---|---|
| randnla#0 | `gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral` (InverseMoments/LambdaMinTail) | `…_lintegral_operator` (OperatorHardEdge) | 4-line proof inlined; `ht` kept as `_ht` (published statement, used at LambdaMinTail:400). Keeper already tagged `wishart-lambda-min-tail` |
| randnla#1 | `choleskyStep`, moved to new **`Matrix/Factorizations/CholeskyStep.lean`** and **generalised to any `[Field K]`** (body unchanged); PSD API over `ℝ` | `choleskyResidualStep` and its API: `_apply`, `posSemidef_`, `posSemidef_sub_`, `_zero`, `_row_eq_zero`, `ker_mulVecLin_le_ker_`, `rank_…_lt` (renamed onto `choleskyStep`; see table) | New in CholeskyStep: `choleskyStep_zero`, `choleskyStep_eq_self_of_apply_self_eq_zero`, `choleskyStep_apply_pivot_{left,right}_of_ne_zero`, `posSemidef_sub_choleskyStep` (square-root-free, no Nyström), `ker_mulVecLin_le_ker_choleskyStep`, `rank_choleskyStep_lt` (Field). The Nyström identity stays in LowRank as `choleskyStep_eq_sub_nystrom` (CholeskyPivot). Over `ℂ`, `choleskyStep` is `complexCholeskyResidualStep` by `rfl` (follow-up below) |
| randnla#2 | `partialCholeskyResidual` (PartialCholesky) | `choleskyResidualHistory`, `posSemidef_choleskyResidualHistory`; `posSemidef_sub_choleskyResidualHistory` → `posSemidef_sub_partialCholeskyResidual` (moved to PartialCholesky), `rank_choleskyResidualHistory_le_sub` → `rank_partialCholeskyResidual_le_sub`, `choleskyResidualHistory_eq_zero_of_rank_le` → `partialCholeskyResidual_eq_zero_of_rank_le` (tag `rpcholesky (partial)` kept) | CholeskyHistories now imports PartialCholesky; RandomPivotedCholesky retargeted. `choleskyHistoryWeight` stays |
| randnla#3 | `sum_complexCholeskyPivotProbability_mul_re_trace_step_eq` (Matrix layer) | `sum_complexCholeskyPivotProbability_mul_trace_step_eq_all` | ComplexCholeskyHistories now imports the Matrix file directly; the 8-line re-export **`LowRank/Cholesky/ComplexCholeskyPivot.lean` deleted** |
| randnla#4 | `sum_choleskyPivotProbability_mul_trace_step_eq` (no `trace ≠ 0` hypothesis; body of the old `_all`, now in CholeskyPivot) | old hypothesis version, `…_eq_all` | |
| randnla#7 | `selectionMatrix` (+ `mul_selectionMatrix`, `transpose_selectionMatrix_mul`, new `transpose_selectionMatrix_apply`) moved to new **`Matrix/Basic/Selection.lean`** | `srhtRowSelector`, `srhtSequenceRowSelector` (replaced inline by `(selectionMatrix (T.val.orderEmbOfFin T.prop))ᵀ` and `(selectionMatrix I)ᵀ`), `srhtRowSelector_mul` (→ `transpose_selectionMatrix_mul`) | SRHTCore, SRHTWithReplacement; `nystrom_selectionMatrix` stays in PartialCholesky |
| randnla#8 | `sampledColumnMatrix`, `sampledRowMatrix` **generalised to `[RCLike 𝕜]`** (real scalar rescaling, body unchanged) | `sampledColumnMatrixReal`, `sampledRowMatrixReal` | `_map_ofReal` bridges restated with the plain names; SamplingMultiplication, SamplingMultiplicationBounds. Optional `leverageSamplingSketch = sampledRowMatrix 1` not done |
| randnla#9 | plain names in SpectralRangeFinder, **`hk : 2 ≤ k` weakened to `1 ≤ k`** in `integrable_and_integral_specNorm_mul_block_mul_pinvR_block_le`, `integral_specNorm_residual_le_of_gaussian`, `…_singularValues_of_gaussian`, `integral_specNorm_residual_gaussianRangeFrame_le`; and `integrable_and_integral_specNorm_pinvR_gaussianMatrix_le` (InverseMoments/SpectralTail, tag `pinv-spectral-expectation`) **generalised `2 ≤ r` → `1 ≤ r`** (the proof already went through the sharp `r ≥ 1` lemma) | the four `_of_pos` copies and `sqrt_one_div_sub_one_le_exp_sqrt_add_one_div`; **`LowRank/RangeFinding/GaussianSpectralEndpoints.lean` deleted** | ExpectedPower uses the plain name. Docstrings record the deviation from HMT (`k ≥ 2` there; one-row endpoint from manuscript `sa:expected-power`) |
| randnla#10 | `measurable_specNorm_of_entries` (Matrix/Structured/SpectralMeasurable) | private `measurable_specNorm_of_entries'` (SpectralRangeFinder) | |
| randnla#11 | ForMathlib `measurePreserving_update_pi (fun _ => gaussianReal 0 1) j` | `measurePreserving_update_pi_gaussianReal` (SmallBall) | |
| randnla#12 | `inv_self_mul_transpose_orthogonal_mul` moved Probe → InverseMoments/DiagonalLaw (imported by both) | private copy in OffDiagonal | use now `simp only [Equiv.apply_symm_apply, Matrix.mul_one, inv_self_mul_transpose_orthogonal_mul U hU]` |
| randnla#13 | public `planeRotation (Pi.single i 1) (Pi.single j 1) (√2)⁻¹ (√2)⁻¹` + `transpose_planeRotation_mul_self` | private 45° `planeRotation`, `planeRotation_transpose_mul` (OffDiagonal) | local private lemmas `planeRotation_single_apply_left`, `…_transpose_mul`, `…_conj_apply` (the conjugation entry); OffDiagonal imports Matrix/Inequalities/PlaneRotation |
| randnla#14 | `integral_le_sqrt_integral_sq` in new **`ForMathlib/MeasureTheory/IntegralSqrt.lean`**, **without the `0 ≤ Y` hypothesis**; `integral_le_of_integral_sq_le` moved there (name kept) and reproved as a 2-line corollary | `Assembly.integral_le_sqrt_integral_sq`, `integral_le_integral_sq_div_add_div_two` | Lipschitz imports the new file (LinearForms, Chevet unchanged); SpectralRangeFinder uses the keeper |
| randnla#15 | `integrable_iSup_of_fintype`, `integrable_iInf_of_fintype` moved verbatim (names kept) to new **`ForMathlib/MeasureTheory/IntegrableSup.lean`** (existing ForMathlib files are P_formathlib's) | — | Lipschitz imports it |
| randnla#16 | `lintegral_of_indepFun`, `integral_of_indepFun` moved verbatim (names kept) to new **`ForMathlib/Probability/Independence.lean`** | — | `atlas: gaussian-conditioning` **removed** from `integral_of_indepFun` (Mathlib-level fact; four other declarations keep that tag). Conditioning imports it; `Estimation/Trace/Unbiased` (P_krylov's) now imports the ForMathlib file instead of RandomMatrix Conditioning (reference edit, built) |
| randnla#18 | `gaussianMatrix_ae_linearIndependent_qrColumnFamily` | `gaussianMatrix_rank_deficient_qr_measure_zero` (unused `ae_iff` form) | HaarQR |
| randnla#20 | `integrable_and_integral_frobSq_sub_sketchedOutput_le_rank_factor_gaussian` | body of `gn_main_gaussian` | `gn_main_gaussian` (same name, statement, `atlas: gn-expected-error` tag) **moved** GaussianSketch → Nystrom/GaussianNystrom as a 9-line corollary via `Assembly.completion_factor_mono` |
| randnla#21 | `trace_mul_moorePenroseInverse`, `mul_transpose_eq_mul_moorePenroseInverse` moved verbatim (names kept) to new **`Matrix/Basic/MoorePenroseProjector.lean`** | — | `Matrix/Basic/MoorePenroseRank.lean` already existed (P_basic's), so a new file instead of appending; Leverage imports it |
| randnla#22 | `exists_eq_transpose_mul_of_posSemidef` moved verbatim to new **`ForMathlib/LinearAlgebra/Matrix/PosSemidef.lean`** (a thin wrapper of Mathlib `CStarAlgebra.nonneg_iff_eq_star_mul_self`, so ForMathlib rather than Matrix) | — | Nystrom/Structural imports it |
| randnla#23 | `sub_mul_pinvR_mul_transpose_eq` moved SpectralRangeFinder → LowRank/Structural/RangeFinder | inline re-proof (`hZ`, `hdiff`) in `frobSq_sub_mul_pinvR_mul_transpose_eq` | |
| Fin/Fintype pairs | `specNorm_gram_sub_one_le_iff_singularValues_sq`, `isSubspaceEmbedding_iff_singularValues` (SingularValueEmbedding) **generalised to arbitrary `Fintype` indices**, list `j : Fin (Fintype.card n)` with no reindexing in the statement | `…_fintype` versions (FiniteIndexTransport) | `atlas: ose-def` moved onto the keeper; Fin base case is a private lemma; `transpose_mul_self_sub_one_reindex` moved into SingularValueEmbedding; no other users |

## Done by another agent

- randnla#17 (`HansonWrightProof.hasSubgaussianMGF_id_gaussianReal_zero_one`): already executed by P_prob
  (probability#15): the general lemma now lives in `Probability/Gaussian/Basic/StandardGaussian.lean`.

## Skipped / deferred, with reasons

- **randnla#19** (`linForm` into `Probability/Gaussian/Basic/GaussianMatrix`, FourthMoment restated
  with `linForm`, `integral_linForm_sq_gaussianMatrix` as the `u = v` corollary) and **randnla#25**
  (FourthMoment's matrix half to RandomMatrix/Gaussian/Moments): both sit in P_prob's file and overlap
  P_prob's probability#47 (moving `gaussianMatrix` and the gaussianMatrix half of FourthMoment to
  RandomMatrix). `NLAlib/RandomMatrix/Gaussian/Basic/GaussianMatrix.lean` did not exist when I got
  there, so per instructions nothing moved. Plan once P_prob's move lands: put `linForm`,
  `linForm_eq_frobInner`, `continuous_linForm` next to `gaussianMatrix` in that file; restate
  `integrable/integral_linear_mul_{two,four}_gaussianMatrix` with `linForm` (curried coefficients);
  reprove `integral_linForm_sq_gaussianMatrix` (3 users) as
  `integral_linear_mul_two_gaussianMatrix` at `u = v` (`Fintype.sum_prod_type'` to uncurry); place
  `integral_frobSq_mul_gaussianMatrix_mul_sq` next to SecondMoment.
- **randnla#5** (real RPCholesky stack vs complex): not cheap. Plan: `choleskyStep` is now
  Field-generic, so (1) replace `complexCholeskyResidualStep` by `choleskyStep` (it is literally
  `choleskyStep (K := ℂ)`, `rfl`; owner of Matrix/Factorizations/ComplexCholeskyPivot), and
  likewise `complexCholeskyResidualHistory` by an RCLike `partialCholeskyResidual`; (2) bridge
  `(choleskyStep R i).map ofReal = choleskyStep (R.map ofReal) i`,
  `choleskyPivotProbability R i = complexCholeskyPivotProbability (R.map ofReal) i`, induct to
  equal history weights and `choleskyExpectedTrace A t = complexCholeskyExpectedTrace (A.map ofReal) t`,
  `spectralTraceTail` via `eigenvalues₀_map_ofReal`; (3) state the real RandomPivotedCholesky
  theorems as one-line corollaries and delete the real CholeskyHistories copies (~45 decls).
- **randnla#6** (volume sampling): leaf stacks, but the real statements use `bestRankFrobSq` /
  `singularValueTailSq`, which the Matrix area has not yet related to `complexBestRankFrobSq` /
  `complexGramTail`; the finding itself says to wait. Plan as in the finding (bridges for
  `volumeSamplingWeight`, `moorePenroseInverse`/`complexColumnProjector` under `map ofReal`,
  `bestRankFrobSq k A = complexBestRankFrobSq k (A.map ofReal)`), then delete the real file and move
  its atlas tags.
- **randnla#24** (`complexSubspaceIterate`, `complexSubspaceTangent`): owners are Krylov
  (`subspaceIterate`) and Matrix (`subspaceTangent`). Plan: generalise `subspaceIterate` to a
  commutative semiring and `subspaceTangent` to `[RCLike 𝕜]` with `ᴴ`, delete the complex copies in
  LowRank/RangeFinding, then merge SubspaceConvergence/ComplexSubspaceConvergence and
  PolynomialFilter/ComplexPolynomialFilter.
- randnla#21 second half: `mul_transpose_eq_mul_moorePenroseInverse_of_qr_of_rank_eq_card`
  (Matrix/Factorizations/QRConsequences, not mine) is now a special case of the moved
  `mul_transpose_eq_mul_moorePenroseInverse` and can be reproved as a corollary (Matrix decision).

## Generalisations

- `choleskyStep` (and its kernel/rank lemmas): `ℝ` → any `[Field K]`.
- `integrable_and_integral_specNorm_pinvR_gaussianMatrix_le`: `2 ≤ r` → `1 ≤ r`.
- HMT 10.6 range-finder theorems in SpectralRangeFinder: `2 ≤ k` → `1 ≤ k`.
- `sampledColumnMatrix`, `sampledRowMatrix`: `ℂ` → `[RCLike 𝕜]`.
- `integral_le_sqrt_integral_sq`: hypothesis `0 ≤ Y` dropped.
- `specNorm_gram_sub_one_le_iff_singularValues_sq`, `isSubspaceEmbedding_iff_singularValues`:
  `Fin` → arbitrary `Fintype` indices.

## Files created / deleted

- Created: `NLAlib/Matrix/Factorizations/CholeskyStep.lean`, `NLAlib/Matrix/Basic/Selection.lean`,
  `NLAlib/Matrix/Basic/MoorePenroseProjector.lean`, `NLAlib/ForMathlib/MeasureTheory/IntegralSqrt.lean`,
  `NLAlib/ForMathlib/MeasureTheory/IntegrableSup.lean`, `NLAlib/ForMathlib/Probability/Independence.lean`,
  `NLAlib/ForMathlib/LinearAlgebra/Matrix/PosSemidef.lean`.
- Deleted: `NLAlib/LowRank/Cholesky/ComplexCholeskyPivot.lean` (re-export shim),
  `NLAlib/LowRank/RangeFinding/GaussianSpectralEndpoints.lean`.
- Aggregators regenerated with `python3 scripts/reorg.py --gen-aggregators`.
  `scripts/AuditNewProofs.lean`: the two deleted modules removed from its list (new files not added).

## Foreign files touched (reference edits only)

`NLAlib/Estimation/Trace/Unbiased.lean` (import: ForMathlib Independence instead of RandomMatrix
Conditioning), `scripts/AuditNewProofs.lean` (module list).

## For the coordinator

- Atlas (`sync_atlas.py`): `wishart-lambda-min-tail` loses `…_lintegral_operator`;
  `gaussian-conditioning` loses `integral_of_indepFun` (cite it as a prerequisite);
  `ose-def` now on the Fintype `isSubspaceEmbedding_iff_singularValues` (the `_fintype` decl is
  gone); `gn-expected-error`'s `gn_main_gaussian` changes module (Nystrom/GaussianNystrom);
  `partial-cholesky-nystrom` (partial) tags unchanged; `pinv-spectral-expectation` and
  `rsvd-spectral-expected` statements now hold for `k ≥ 1`.
- `docs/REORG_FOLLOWUP.md` still mentions GaussianSpectralEndpoints and the LowRank
  ComplexCholeskyPivot shim.

## Compilation

`lake build` of NLAlib.LowRank, NLAlib.RandomMatrix, NLAlib.Sketching.{Sampling,Structured,Properties},
NLAlib.Estimation.Trace, NLAlib.Krylov.Quadrature.SpectralMeasure, NLAlib.Sketching.Sparse.{SparseFiniteIndex,
CountSketchExpectation} and every created file: all build (only the pre-existing
`partialCholeskyFactor_mul_transpose_eq_nystrom` scaffold `sorry`). `check_layers.py` and
`check_names.py` pass.

## Summary

20 of 26 findings executed here and one (#17) already done by P_prob, plus the Fin/Fintype
subspace-embedding pair collapse. Two findings (#19, #25) wait for P_prob's `gaussianMatrix` move.
Three real/complex twin findings (#5, #6, #24) are left as follow-ups with plans. 7 files created, 2 deleted, 33
renames recorded.
