# Dedup round phase 2, agent P_norms (Matrix/Norms, Matrix/Inequalities)

Rename table: `docs/renames/2026-10-12-dedup-P_norms.json` (32 entries).

## Findings executed

| finding | keeper (home) | dropped | notes |
|---|---|---|---|
| matrix_norms#0 | `exists_specNorm_le_one_frobInner_eq_nuclearNorm` (Norms/NuclearNorm) | `exists_specNorm_le_one_frobInner_eq_nuclearNorm_polar`, `…_polar_fin`, `IsSVD.polarSingularCoefficients_attain` (SchattenDuality) | keeper now proved directly over Fintype from the Ky Fan attainment frames (`U Vᵀ`), no Fin step. `polarSingularCoefficients` + nonneg/antitone/rank lemmas kept |
| matrix_norms#1–#6 | `nuclearNorm_le_rank_mul_specNorm`, `frobNorm_le_nuclearNorm`, `nuclearNorm_le_sqrt_rank_mul_frobNorm`, `frobInner_le_nuclearNorm_of_specNorm_le_one`, `exists_specNorm_le_one_frobInner_eq_nuclearNorm`, `isGreatest_nuclearNorm_frobInner` | the six `_fin` names | **NuclearFiniteIndex.lean merged into NuclearNorm.lean** (file deleted). Four Fin steps are `private` in NuclearNorm; the Fin attainment and Fin `isGreatest` are deleted outright (general proofs need no Fin step) |
| matrix_norms#7–#11 | `kyFanNorm_add_le`, `kyFanNorm_smul`, `kyFanNorm_orthogonal_mul`, `kyFanNorm_mul_orthogonal`, `kyFanNorm_transpose` | the five `_fin` names | **KyFanFiniteIndex.lean merged into KyFanNorms.lean** (file deleted). Only `kyFanNorm_add_le_fin` survives, `private`; smul/orthogonal/transpose are proved directly over Fintype from the (now Fintype) `singularValues_*` invariances. Tag `ky-fan-norms-def (partial)` moved from `kyFanNorm_add_le_fin` to `kyFanNorm_add_le` |
| matrix_norms#12–#15 | `schattenNorm_orthogonal_mul`, `schattenNorm_mul_orthogonal`, `schattenNorm_transpose`, `schattenNorm_two` | the four `_fin` names | Fintype invariances **moved SchattenInvariant → Schatten** (next to the def), Fin copies deleted; `schattenNorm_two_fin` is `private` |
| matrix_norms#16, #17 | `exists_schattenNorm_le_one_frobInner_eq`, `exists_nuclearNorm_le_one_frobInner_eq_specNorm` | `…_fin` | Fin steps `private` in SchattenDuality |
| matrix_norms#18 | `trace_twoSided_compression_le_kyFanNorm` (now Fintype, Inequalities/KyFan) | `trace_twoSided_compression_le_kyFanNorm_fintype` | Fin version `private` in KyFan. `kyFanNorm_reindex` (from KyFanNorms) and `twoSided_compression_trace_reindex` (from KyFanTrace) moved into KyFan |
| matrix_norms#19 | `exists_trace_twoSided_compression_eq_kyFanNorm` (now Fintype, KyFanAttainment) | `…_fintype` | Fin version `private`. **KyFanTrace.lean deleted** (empty). KyFanToolkit contract updated |
| matrix_norms#23, #24, #25 | `sum_eigenvalues_eq_sum_sorted`, `eigenvalues₀_nonneg_of_posSemidef`, `spectralTraceTail`, `spectralTraceTail_nonneg`, `spectralTraceTail_le_trace` (`≤ RCLike.re A.trace`), `rank_le_of_spectralTraceTail_eq_zero`, all `[RCLike 𝕜]` (Inequalities/TraceTail, now `open scoped ComplexOrder`) | `complex_sum_eigenvalues_eq_sum_sorted`, `complex_eigenvalues₀_nonneg_of_posSemidef`, `complexSpectralTraceTail`, `complexSpectralTraceTail_nonneg`, `complexSpectralTraceTail_le_trace`, `complex_rank_le_of_spectralTraceTail_eq_zero` | The energy bound has a new RCLike core `sq_max_re_trace_sub_spectralTraceTail_le_of_eigenvalues₀_le` (takes the eigenvalue domination as hypothesis); `sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq` (ℝ) and `complex_sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq` (ℂ) remain as 2-line wrappers supplying Loewner monotonicity, because eigenvalue monotonicity exists only separately for ℝ (CourantFischer) and ℂ (`complex_eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub`, ComplexTraceTail). Once matrix_spectral#35 (RCLike Courant–Fischer) lands, the two wrappers collapse to one. ComplexTraceTail no longer imports TracePowers. LowRank/Cholesky/ComplexRandomPivotedCholesky: reference edits only (its theorem names that contain `complexSpectralTraceTail` were not renamed) |
| matrix_norms#26 | `specNorm_le_of_mulVec_sq_le` (moved EuclideanOperatorBounds → Norms/SpectralNormBounds) | `specNorm_le_of_forall_sum_sq_mulVec_le` | its only user (`specNorm_blockDiagonal_const_le`) converts with `simp only [dotProduct, ← sq]`; the HutchinsonTail user had already gone (F2b) |
| matrix_pert#36 | `cfc_eq_eigenvectorUnitary_mul_diagonal_mul_transpose` (Functions/CFCTrace) | `cfc_eq_mul_diagonal_eigenvalues_mul_transpose` (NuclearHermitian) | use rewritten `rw [hA.cfc_eq, cfc_eq_eigenvectorUnitary_…]` |
| RankNorm (coordinator; = matrix_spectral#20) | `frobSq_le_rank_mul_specNorm_sq`, `frobNorm_le_sqrt_rank_mul_specNorm` now over `[Fintype m] [Fintype n]` (RankNorm imports Norms/Reindex) | `frobSq_le_rank_mul_specNorm_sq_fintype`, `frobNorm_le_sqrt_rank_mul_specNorm_fintype` (deleted from Spectral/FiniteIndexTransport) | Fin step `private`; tag `atlas: norms-frob-spec` carried by the keeper. Users renamed: VonNeumann, Perturbation/OptimalErrorContinuity |
| (collision) | `singularValues_le_specNorm` (Fintype, P_spectral's, Spectral/SpectralBounds) | Fin `singularValues_le_specNorm` in RankNorm deleted | P_spectral re-declared the name in SpectralBounds (matrix_spectral#19), which RankNorm imports; same name, no rename entry |

## Skipped

- matrix_norms#20, #21, #22: already done in phase 1 (F2c).
- matrix_norms#27 (Hanson–Wright norm defs): P_prob's, per instructions.
- matrix_norms#31 (`rectangularDiagonal` / `rectangularDiagonalMatrix` / `rectDiag`): low priority; the bridge
  `rectangularDiagonalMatrix (m := Fin m) (n := Fin n) x = rectangularDiagonal (x ∘ Fin.cast _)` needs
  `Fintype.equivFin (Fin m)` to act as the identity, which is not definitional and has no Mathlib lemma.
  Left as is: `rectangularDiagonal` is the Fin thin-vector embedding (defined via `rectDiag`), and
  `rectangularDiagonalMatrix` its Fintype transport (defined via `rectangularDiagonal` and `reindex`).

## Files

- Deleted: `Matrix/Norms/NuclearFiniteIndex.lean`, `Matrix/Inequalities/KyFanFiniteIndex.lean`,
  `Matrix/Inequalities/KyFanTrace.lean`. Aggregators regenerated with `scripts/reorg.py --gen-aggregators`
  (also picked up other agents' pending file changes). Entries removed from `scripts/AuditNewProofs.lean`.
- Import retargets (foreign files, import-only): Factorizations/StrongRankRevealingQR,
  Spectral/OstrowskiCongruence, Subspaces/ObliqueCanonicalSpectrum (KyFanFiniteIndex → KyFanNorms).
- Reference edits (foreign): Spectral/FiniteIndexTransport (two `_fintype` declarations deleted, as
  instructed), Perturbation/OptimalErrorContinuity, LowRank/Cholesky/ComplexRandomPivotedCholesky.

## For the coordinator

- Atlas: re-run ExtractDecls / sync_atlas; atlas.json still names modules KyFanTrace / KyFanFiniteIndex
  (generated side).
- docs/REORG_FOLLOWUP.md line ~200 still describes the old KyFan chain (KyFanFiniteIndex, KyFanTrace).

## Compilation

`lake build` of 40 targets, all green: every edited module, the `NLAlib.Matrix.Norms` and
`NLAlib.Matrix.Inequalities` aggregators (so every Norms/Inequalities file), and every module
referencing a changed or moved name: LowRank/Cholesky/{RandomPivotedCholesky, ComplexRandomPivotedCholesky},
Factorizations/{MaximumVolumeRankAdapted, Procrustes, ProcrustesRotations, ScaledOrthogonal,
StrongRankRevealingQR}, Perturbation/{GoldenRatioBlock, OptimalErrorContinuity},
Spectral/{FiniteIndexTransport, OstrowskiCongruence}, Subspaces/{ObliqueCanonicalSpectrum, ProjectionGaps}.
A first build was blocked by other agents' in-progress edits (SingularValueInvariance, CourantFischer,
EckartYoung, RealDilation, QR); the rebuild after they went green passed. No new `sorry`.
`check_names.py` OK; `check_layers.py` reports only the pre-existing RademacherMgfCgf → HutchinsonLaws violation.
