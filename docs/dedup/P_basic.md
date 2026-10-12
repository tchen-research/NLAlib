# Dedup round, agent P_basic (Matrix/Basic, Subspaces, Structured, Calculus)

Rename table: `docs/renames/2026-10-12-dedup-P_basic.json` (13 entries).

## Findings executed

| Finding | Keeper (home) | Dropped | Notes / files touched |
|---|---|---|---|
| matrix_basic#7 | `rank_add_le` (Basic/RankBounds) | `rank_sum_le_sum_rank` (Basic/RankInequalities) | tag `rank-inequalities` and the HJ §0.4.2 citation moved to `rank_add_le`. RankInequalities no longer used RankBounds and now imports `Mathlib.LinearAlgebra.Matrix.Rank` instead |
| matrix_basic#9 | Mathlib `Matrix.isHermitian_iff_isSymm` | `isHermitian_of_isSymm`, `isSymm_of_isHermitian` (Basic/SchurComplement) | `.mpr` / `.mp` at the uses: SchurComplement, GeneralizedSchurComplement, Spectral/SylvesterCriterion (reference edit), Inequalities/HadamardDeterminantLower (reference edit) |
| matrix_basic#10, #11 | `posSemidef_fromBlocks_iff`, `dotProduct_schurComplement_mulVec_eq` (Basic/GeneralizedSchurComplement) | `posSemidef_fromBlocks_iff_generalized_schur`, `dotProduct_generalized_schur_minimizer_eq` | The whole Albert section moved from SchurComplement to GeneralizedSchurComplement: `def schurComplement` now opens that file, and every statement there (`dotProduct_fromBlocks_eq_generalized_schur_square`, `posSemidef_fromBlocks_iff`, `isLeast_generalized_schur_quadratic`, `generalized_schur_nonneg_and_le`, the bundle `generalized_schur_complement`) is phrased with `schurComplement A B C` in place of `C - Bᵀ * A⁺ * B`. `dotProduct_schurComplement_mulVec_le` (convenience corollary) and `posSemidef_sub_schurComplement` (needs only `A ⪰ 0`) moved along. The bundle's minimiser clause now reads in the keeper's orientation `xᵀ(M/A)x = (−A⁺Bx, x)ᵀ M (−A⁺Bx, x)` (with `-(A⁺ * B) *ᵥ x`). Tags: the keeper already carried `generalized-schur-complement-psd (partial)`; the bundle keeps the full tag. SchurComplement.lean is now the pivot (elimination/Cholesky step) file only and no longer imports GeneralizedSchurComplement; no file outside these two used any Albert name |
| matrix_basic#12 | `transpose_residual_mul_residual_eq_one_sub_overlap` (Subspaces/ProjectionGaps), **generalised** to `P : Matrix m n ℝ`, `Q : Matrix m p ℝ` (proof unchanged) | `transpose_residual_mul_residual_eq_one_sub_overlap_of_unequal_widths` (Subspaces/PrincipalAngleBridges) | use in `specNorm_residual_sq_eq_one_sub_sigmaMin_sq` retargeted; existing equal-width uses (ProjectionGaps, PrincipalAngleDefinitions, PrincipalAngleTangent) elaborate unchanged |
| matrix_basic#13 | `specNorm_residual_sq_eq_one_sub_sigmaMin_sq` (PrincipalAngleBridges), `specNorm_residual_comm`, `specNorm_sub_frame_projector_eq_residual` (ProjectionGaps) | `sq_sinThetaMax_eq_one_sub_sq_sigmaMin`, `sinThetaMax_comm`, `sinThetaMax_eq_specNorm_sub` (Subspaces/PrincipalAngles) | `principal-angles-def (partial)` added to `specNorm_residual_sq_eq_one_sub_sigmaMin_sq` (the other two keepers had it); GVL Thm 2.5.1 / Stewart–Sun Thm I.5.5 citations and the "false for unequal widths" remark moved onto the keepers. In-file uses (`sinThetaMax_eq_sqrt_one_sub_sq_singularValues`, `sinThetaMax_lt_one_iff_isUnit`) take the keeper through a typed `have` (`sinThetaMax` unfolds to `specNorm (residual Q X)`). `sinThetaMax` itself is kept (see below) |
| matrix_basic#14 | `principalAnglesFintype` (Subspaces/PrincipalAngleDefinitions) | `principalAngles` (Fin r / Fin r', ℕ-indexed) and the bridge `principalAnglesFintype_eq_principalAngles` (PrincipalAngles) | first option of the finding: `sinThetaMax_eq_sin_principalAngles` restated for equal widths, `sinThetaMax Q Q' = sin (principalAnglesFintype Q Q' ⟨card k − 1, _⟩)` for `0 < card k` (proof: `specNorm_sinePrincipalAngles_eq_residual` + `specNorm_sinePrincipalAngles_eq_sin_last`); the unequal-width case stays as `sinThetaMax_eq_sqrt_one_sub_sq_singularValues`. GVL §6.4.3 citation added to `principalAnglesFintype`. Nothing outside PrincipalAngles.lean used `principalAngles` |
| matrix_basic#15 | `measurable_inv_entry_of` (moved verbatim, with `measurable_pow_entry_of`, `measurable_trace_of_entries`, from Structured/GramSoftMinMeasurable to Structured/Measurable, next to `measurable_mul_entry_of`; section variables `Ω`, `ι` turned into explicit binders over the file's `γ`) | `measurable_nonsing_inv_entry_of` (Subspaces/PolarFrame) | `gn-expected-error` prose moved to the keeper's docstring; Measurable's module doc lists the three lemmas |
| matrix_basic#30 | `specNorm_mul_transpose_right_of_hasOrthonormalCols` (Norms/SpectralNormBounds) | `specNorm_mul_of_transpose_mul_self_eq_one` (PrincipalAngles) | single use in `tanThetaMax_congr_left`: keeper applied to `P := Wᵀ` with `Wᵀᵀ Wᵀ = W Wᵀ = 1` after `conv_rhs => rw [← Matrix.transpose_transpose W]` (a bare defeq `exact` timed out in `whnf`) |

## Already done / skipped

* matrix_basic#17, #18 (`moorePenroseInverse_eq_nonsing_inv`, `moorePenroseInverse_mul_of_hasOrthonormalCols`): already executed by P_pert (its #3, #4); both names are gone.
* matrix_basic#2 (`HansonWrightProof.matrixQuadraticForm`): already gone from the tree (no occurrence left).
* matrix_basic#3 (`SparseFock.MatrixTail.quadraticForm`) and #4 (`SparseFock.HeavyBandsConcrete.quadratic`, `SparseFock.LightSectorConcrete.quadratic`): **skipped**. All three definitions and all their uses live in `Sketching/Sparse/SparseFock/*` (no owner among the phase-2 agents), and the change is not a mechanical reference edit (restating `opNorm_le_iff_quadraticForm` over `quadForm A x.ofLp`, bridge lemmas, rewriting proofs that unfold `quadratic`). Still valid; for the Sketching owner or a follow-up round.

## Vocabulary decision left open

`sinThetaMax Q X := specNorm (residual Q X)` and `tanThetaMax` are kept: the remaining `sinThetaMax_*` lemmas (basis independence, complement form, `sin`–`tan`, invertibility criterion) and the `tanThetaMax` API are not duplicated elsewhere, and nothing outside PrincipalAngles.lean uses `sinThetaMax`. Whether to retire `sinThetaMax` in favour of `specNorm (residual Q X)` is a vocabulary call for the coordinator.

## Splits (files over 500 lines)

* `Matrix/Basic/MoorePenrose.lean` (543 → 345 lines): the structure `IsMoorePenroseInverse` and its namespace (uniqueness, `swap`, `transpose`, `submatrix`, `orthogonal_transform`, projector idempotence and range, `transpose_mul_self`; pure algebra, no SVD) moved verbatim to the new **`Matrix/Basic/PenroseIdentities.lean`** (223 lines, imports only `Mathlib.LinearAlgebra.Matrix.ToLin` and `Mathlib.Data.Real.Basic`). MoorePenrose imports it, so no dependant needed an edit.
* `Matrix/Subspaces/Projections.lean` (542 → 486 lines): the section "An orthonormal basis matrix for any subspace" (`orthonormalBasisMatrix`, `hasOrthonormalCols_orthonormalBasisMatrix`, `range_orthonormalBasisMatrix`, tag `orthonormal-basis-matrix`, plus two private helpers) moved verbatim to the new **`Matrix/Subspaces/OrthonormalBasisMatrix.lean`** (76 lines, imports Projections). Its four users got the import: ProjectionGaps (covers ObliqueProjectionSecant transitively), ObliqueProjectionBlocks, and Krylov/Solvers/GMRES (reference edit: its `import …Projections` replaced by `import …OrthonormalBasisMatrix`).

## Files created / deleted

* Created: `NLAlib/Matrix/Basic/PenroseIdentities.lean`, `NLAlib/Matrix/Subspaces/OrthonormalBasisMatrix.lean`. Aggregators regenerated with `python3 scripts/reorg.py --gen-aggregators` (93 aggregators).
* Deleted: none.

## Foreign files touched (reference edits only)

`Matrix/Spectral/SylvesterCriterion.lean` (Mathlib `isHermitian_iff_isSymm`, two lines rewrapped), `Matrix/Inequalities/HadamardDeterminantLower.lean` (same), `Krylov/Solvers/GMRES.lean` (import).

## For the coordinator

* Atlas: re-run ExtractDecls/sync_atlas. Moved tags: `rank-inequalities` now on `rank_add_le`; `principal-angles-def (partial)` added to `specNorm_residual_sq_eq_one_sub_sigmaMin_sq`; the `principalAngles` def's tag is subsumed by `principalAnglesFintype` (already tagged).
* `docs/KRYLOV_DEFINITIONS.md` and `docs/ROUND8_KRYLOV_BRIEF.md` still place `orthonormalBasisMatrix` in `Matrix/Projections` (historical docs, not edited).
* SparseFock quadratic-form findings (#3, #4) remain open.

## Compiled

`lake build` (one invocation, 4299 jobs, success) of the touched modules (PenroseIdentities, MoorePenrose,
Structured/Measurable, Projections, RankBounds) and the 31 maximal modules of the reverse-import
closure (154 modules) of SchurComplement, GeneralizedSchurComplement, RankInequalities,
ProjectionGaps, PrincipalAngleDefinitions, PrincipalAngleBridges, PrincipalAngles,
GramSoftMinMeasurable, PolarFrame, OrthonormalBasisMatrix, SylvesterCriterion,
HadamardDeterminantLower and GMRES (e.g. GMRESArnoldi, PowerMethod, SubspaceIteration,
RandomPivotedCholesky, RawGaussianNystrom, CholeskyToolkit, LULeadingRank, QRDecomposition,
StrongRankRevealingQR, HadamardToolkit, DeterminantInequalityToolkit, SylvesterCriterionToolkit,
StructuredToolkit, CauchyDeterminantFinite, CSToolkit, ComplexCSToolkit, PseudoinversePerturbation,
WedinFiniteIndex, GaussianWeakInequality); then the aggregators `NLAlib.Matrix.Basic`,
`NLAlib.Matrix.Subspaces`, `NLAlib.Matrix.Structured`. No new `sorry`. `check_names.py` passes;
`check_layers.py` reports only the pre-existing `RademacherMgfCgf` → `HutchinsonLaws` violation.
