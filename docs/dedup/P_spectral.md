# Dedup round, phase 2, agent P_spectral (Matrix/Spectral)

Rename table: `docs/renames/2026-10-12-dedup-P_spectral.json` (24 entries). No files created or
deleted (aggregators unchanged).

## Findings executed

| finding | keeper (now) | dropped | files touched |
|---|---|---|---|
| F1 #9 | `singularValues_zero_eq_specNorm` (SpectralBounds, now Fintype; Fin proof kept as private base, transported with `singularValues_reindex`/`specNorm_reindex`) | `singularValues_reindex_zero_eq_specNorm` (FiniteIndexTransport) | users KyFanNorms, ConditionNumber, ComplexSingularTransport, ObliqueProjectionNorms (its private `native_singularValue_zero_eq_specNorm` is now a one-line alias of the keeper) |
| #19 | `singularValues_le_specNorm` (moved RankNorm → SpectralBounds, Fintype) | `toEuclideanLin_singularValues_le_specNorm` (SchattenTrace) | SchattenTrace, SchattenComparison |
| F1 #8 | `sigmaMin_eq_singularValues_last (A : Matrix m n ℝ) (hn : 0 < card n) : sigmaMin A = singularValues A (card n - 1)` (SpectralBounds, Fintype; Fin base private); `sigmaMin_pos_iff_rank_eq_width` also Fintype (`A.rank = card n`); `sigmaMin_reindex` moved SigmaMinTransport → SpectralBounds | `sigmaMin_eq_toEuclideanLin_singularValues_last` | Conditioning, PrincipalAngles, PrincipalAngleBridges (Fin callers get `Fintype.card_fin`) |
| #32 | `sigmaMin_pos_iff_isUnit_of_nonempty` (moved PrincipalAngleBridges → SigmaMinTransport, reproved in 3 lines from the Fintype rank criterion) | `sigmaMin_pos_of_isUnit` (OstrowskiCongruence) | OstrowskiCongruence |
| F1 #38 | `sq_sigmaMin_mul_dotProduct_le_mulVec_dotProduct` generalised to rectangular and moved to Spectral/Core; `sigmaMin_transpose_eq` moved to SigmaMinTransport (now 2-line proof) | — | OstrowskiCongruence. (`quadForm_mul_mul_transpose` no longer exists; Ostrowski uses `quadForm_transpose_mul_mul` from QuadForm, so that part was moot.) |
| #15 | `singularValues_eq_zero_of_{height,width,min}_le` (SVD) now RCLike/Fintype with `Fintype.card` bounds | `toEuclideanLin_singularValues_eq_zero_of_min_le` (SchattenProducts) | Fin callers adapted with `simpa only [Fintype.card_fin]`: SVD, SvdBlocks, SvdPowers, EckartYoung, SingularValueScaling, SingularValueInvariance, RealDilation, SpectralBounds, RankNorm, KyFan, KyFanNorms, MirskyPadded, RectangularDiagonalPermutation, SchattenDuality, RankRevealingTrailing, ObliqueCanonicalSpectrum, WedinFiniteIndex, LowRank/RandomizedSVD/OptimalError |
| #16 | `singularValues_eq_zero_of_rank_le` (already general) | `toEuclideanLin_singularValues_eq_zero_of_rank_le` (SchattenComparison) | SchattenComparison |
| #17 | `frobSq_eq_sum_sq_singularValues` (Fintype, `range (min (card m) (card n))`; moved SVD → SingularValueSpectrum, which can reindex; Fin proof private) | `frobSq_eq_sum_toEuclideanLin_singularValues_sq` (ProcrustesRotations) | ProcrustesRotations, Schatten (`schattenNorm_two_fin` `change` line), RankNorm, PrincipalAngleDefinitions |
| #18 | `singularValues_le_of_forall_mem`, `le_singularValues_of_forall_mem`, `exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul`, `exists_submodule_sq_singularValues_mul_le_mulVec_dotProduct` (CourantFischer, Fintype; proofs were index-free) | `le_toEuclideanLin_singularValues_of_forall_mem` (RankRevealingTrailing) | RankRevealingTrailing |
| #12, #13, #14, pert#47 | Weyl.lean generalised to Fintype: `singularValues_add_add_le`, `_add_le_add_specNorm`, `_le_singularValues_add_add_specNorm`, `abs_singularValues_add_sub_le_specNorm`, `singularValues_mul_le_specNorm_mul`, `singularValues_mul_le_mul_specNorm`, `singularValues_residual_le`, `singularValues_le_specNorm_sub_of_rank_le`; Mirsky `sum_sq_singularValues_add_sub_le_frobSq` (Fin base private, reindex transport). Only `isLeast_specNorm_sub_of_rank_le` stays Fin (`truncatedSVD`) | `toEuclideanLin_singularValues_mul_le_mul_specNorm`, `toEuclideanLin_singularValues_mul_le_specNorm_mul` (SchattenProducts), `toEuclideanLin_singularValues_le_specNorm_sub_of_rank_le` (RankRevealingLeading), `sum_singularValues_sub_sq_le_frobSq_sub` (ProcrustesRotations) | SchattenEndpoints, RankRevealingLeading, ProcrustesRotations |
| pert#47 | `conditionNumber_eq_singularValues_ratio` (ConditionNumber, now Fintype, proof via `specNorm_moorePenroseInverse_eq_fintype`) | `conditionNumber_eq_toEuclideanLin_singularValues_ratio` | ConditionNumber, ConditionNumberToolkit |
| pert#47 | `singularValues_eq_of_qr` (QRConsequences, now Fintype, function equality) | `toEuclideanLin_singularValues_eq_of_qr` | QRConsequences, QRDecomposition (`congrFun`) |
| F1 leftover (SchattenTrace `_fin`) | `abs_frobInner_le_sum_singularValues_mul` (Fintype, `singularValues` spelling) | `abs_frobInner_le_sum_toEuclideanLin_singularValues_mul`; `abs_frobInner_le_sum_singularValues_mul_fin` made private | SchattenTrace, ProcrustesRotations |
| #21 | `eigenvalues₀_eq_of_matrix_eq` (EigenvalueEquality) | `eigenvalues₀_eq_of_eq` (SingularValueSpectrum) | SingularValueSpectrum, GramSingularValues, FunctionalCalculusEigenvalues, Mirsky, EigenvaluePencil, EigenvalueVariation |
| #22 | `eigenvalues₀_eq_of_charpoly_eq` (RCLike, EigenvalueEquality); `eigenvalues₀_reindex` (from SingularValueSpectrum) and `eigenvalues₀_map_ofReal` (from ComplexSingularTransport) moved verbatim to EigenvalueEquality | `complex_eigenvalues₀_eq_of_charpoly` | ComplexSingularTransport |
| (spelling) | `singularValues_eq_of_gram_charpoly_eq`, `singularValues_eq_of_gram_eq` (GramSingularValues, now RCLike, `singularValues` spelling) | `complex_singularValues_eq_of_gram_charpoly`, `toEuclideanLin_singularValues_eq_of_gram_eq` | SingularValueInvariance, QRConsequences, NearestPolar, NuclearGram, NuclearHermitian, ObliqueCanonicalSpectrum, ObliqueComplementSpectrum |
| #25 | `aeval_mul_eq_mul_aeval_of_mul_eq` (Functions/PolynomialIntertwining; received tag `atlas: sylvester-equation (partial)` and the HJ Lemma 2.4.4.0 citation) | `aeval_intertwines` | SylvesterQualitative, SylvesterToolkit |
| #26 | `posDef_fromBlocks_iff_posDef_and_schur` (moved BlockOrderConsequences → HaynsworthInertia; tags `haynsworth-inertia-additivity (partial), psd-block-contraction (partial)`) | `posDef_fromBlocks_iff_posDef_schur` (now private proof step) | BlockStrictContraction, BlockOrderConsequences |
| #29 | `det_one_add_X_smul_eq_of_diagonalization` (CommRing, moved ComplexVolumeSpectrum → PrincipalMinors) and new `sum_det_principal_minors_eq_sum_prod_of_diagonalization` (CommRing, `V * U = 1`) | `det_one_add_X_smul_eq_of_orthogonal_diagonalization`, `sum_det_principal_minors_eq_sum_prod_of_orthogonal_diagonalization` (the ℝ case is the instance `V = Uᵀ`) | PrincipalMinors, ComplexVolumeSpectrum (now imports PrincipalMinors; `…_of_isHermitian` is a one-line corollary), LowRank/Sampling/VolumeSampling |

## Findings already done / done by others

* #20 (`frobSq_le_rank_mul_specNorm_sq`, `frobNorm_le_sqrt_rank_mul_specNorm` Fintype, `_fintype` copies
  dropped): done concurrently by P_norms in RankNorm/FiniteIndexTransport (in their rename table). I only
  adapted RankNorm's Fin helpers to the Fintype SVD lemmas.
* #33 (`realDilation`): no longer exists; the RealDilation files already use `dilation`.
* #39 (ComplexEckartYoung importing LowRank): fixed by F2c.

## Skipped, with reasons

* #27 (`rank_eq_card_nonzero_of_orthogonal_diagonalization`, Structured/KroneckerNormRank): needs
  `rank_eq_card_nonzero_of_diagonal_congruence` moved into Matrix/Basic (or Structured importing
  Spectral/SemidefiniteCongruence); both foreign/structural. Both proofs are 4 lines. Low priority.
* #30, #31 (Schur triangularization re-derivations): the inductions live in `ForMathlib/Analysis/*`
  (foreign); a re-proof is not a reference edit.
* #35 (RCLike Courant–Fischer): long-term rewrite (~650 lines), out of scope for this round.
* #40 (`map_ofReal_matrix_pow` → `Matrix.map_pow A Complex.ofRealHom k`): the reviewer's claim is
  wrong for the actual uses. `Matrix.map_pow` states `(M ^ a).map ⇑f = …`, and `rw`/`simp` do not match
  `⇑Complex.ofRealHom` against `Complex.ofReal` (checked on a scratch file: "did not find an
  occurrence"). All 6 uses are `rw`/`simp`, so the NLAlib bridge (a one-line `map_pow` proof) stays.

## Raw-spelling pass

Now spelled with `singularValues A k` (statements): GramSingularValues, SigmaMinTransport,
QRConsequences, ConditionNumber, SchattenTrace (`abs_frobInner_le_sum_singularValues_mul`), and every
generalised keeper above. **Remaining:** 179 raw `(toEuclideanLin A).singularValues` occurrences in
49 files (about 182 before; the Fintype keepers removed the copies, not the consumers' spelling), and
11 `…toEuclideanLin_singularValues…`-named theorems:
`toEuclideanLin_singularValues_map_ofReal` (Spectral/ComplexSingularTransport, mine, kept because
ComplexObliqueSecant and ComplexIdempotentRealForm rewrite raw-spelled goals with it),
`toEuclideanLin_singularValues_eq_eigenvalues₀_of_posSemidef` (Functions), `sum_range_…_mul_rpow_le`
(HornPowerSums), `sum_abs_…`, `weaklyMajorized_abs_…_padded` (MirskyPadded), `weaklyMajorized_abs_…`
(Mirsky), `weaklyMajorized_…_add` (KyFanSums), two `multiset_…` (Structured/KroneckerSingularValues),
`sum_range_…_rpow_eq_of_min_le` (SchattenProducts), `toEuclideanLin_singularValues_cfc_abs`
(NuclearHermitian). The Inequalities ones have Fin twins in the same P_norms files; collapsing them
means generalising those keepers there. The ComplexSingularTransport ℂ lemmas
(`complex_singularValues_{isometry_mul,mul_unitary,zero_eq_norm}`, `rank_eq_of_complex_real_…`) and
three existence statements (`exists_orthogonal_transpose_mul_mul_eq_diagonal_singularValues`,
`exists_unitary_conjTranspose_mul_mul_eq_diagonal_singularValues`, `exists_complex_rectangular_svd`)
are still raw-spelled. Their consumers in Subspaces (CS/oblique) manipulate the raw form, so respelling
them is a follow-up together with an RCLike `HasOrthonormalCols` (which would merge
`complex_singularValues_isometry_mul` with `singularValues_isometry_mul`).

## Foreign files touched (reference-level)

Norms/{RankNorm, Schatten, SchattenProducts, SchattenComparison, SchattenTrace, SchattenEndpoints,
SchattenDuality, RectangularDiagonalPermutation, NuclearGram, NuclearHermitian},
Inequalities/{KyFan, KyFanNorms, Mirsky, MirskyPadded, BlockStrictContraction, BlockOrderConsequences},
Factorizations/{RankRevealingLeading, RankRevealingTrailing, ProcrustesRotations, QRConsequences,
QRDecomposition, NearestPolar}, Perturbation/{ConditionNumber, ConditionNumberToolkit, Conditioning,
EigenvaluePencil, EigenvalueVariation, WedinFiniteIndex}, Functions/{FunctionalCalculusEigenvalues,
PolynomialIntertwining (docstring/tag only)}, Subspaces/{PrincipalAngleBridges, PrincipalAngles,
PrincipalAngleDefinitions, ObliqueProjectionNorms, ObliqueCanonicalSpectrum,
ObliqueComplementSpectrum}, LowRank/{RandomizedSVD/OptimalError, Sampling/VolumeSampling}.
Three are more than renames, each a deletion of a duplicate whose keeper now lives upstream:
ConditionNumber (keeper's binders generalised plus copy deleted), QRConsequences (same), and
BlockOrderConsequences (keeper cut, now in HaynsworthInertia).

## Compiled

`lake build` green for every touched module (63 Matrix modules + OptimalError, VolumeSampling,
OptimalErrorContinuity) and every other user of a changed keeper (CauchyBinet, GramCutoffCalculus,
BlockContractionToolkit, FischerDeterminant, HornPowerSums, HornProductToolkit,
OverlappingBlockDeterminant, NuclearNorm, PseudoinverseNormControl, Wedin, ProductSingularValues,
StrongRankRevealingQR, MaximumVolumeRankAdapted, VonNeumann, CSDecomposition,
ComplexCSDecomposition, ComplexObliqueCanonical). No new `sorry`. `check_names.py` OK;
`check_layers.py` reports only the pre-existing `RademacherMgfCgf → HutchinsonLaws`.

## For the coordinator

* Atlas: re-run ExtractDecls/sync_atlas. Tags moved: `sylvester-equation (partial)` onto
  `aeval_mul_eq_mul_aeval_of_mul_eq`; `haynsworth-inertia-additivity (partial)` onto
  `posDef_fromBlocks_iff_posDef_and_schur` (which keeps `psd-block-contraction (partial)`).
* Follow-ups: #27, #30, #31, #35 above; the raw-spelling remainder.
