# Dedup round, agent P_pert (Perturbation, Factorizations, Functions, OperatorTheory)

Rename table: `docs/renames/2026-10-12-dedup-P_pert.json` (45 entries).

## Findings executed

| Finding | Keeper (home) | Dropped | Notes / files touched |
|---|---|---|---|
| matrix_pert#0 | `conditionNumber_eq_mul_specNorm_inv` (ConditionNumber) | `conditionNumber_eq_of_isUnit` | tag `condition-number-def (partial)` + TB eq. (12.13), GVL eq. (2.6.4) moved; Conditioning's two uses retargeted |
| #1 | `conditionNumber_mul_left_of_hasOrthonormalCols` | `conditionNumber_mul_of_hasOrthonormalCols` | keeper already tagged; GVL §5.3.2 citation added |
| #2 | `conditionNumber_eq_singularValues_ratio` | `conditionNumber_eq_singularValues_div` | GVL §5.5.2 citation added |
| #3 | `moorePenroseInverse_eq_inv_of_isUnit` (Basic/MoorePenroseTransformations) | `moorePenroseInverse_eq_nonsing_inv` | reference edit in Subspaces/ObliqueFrameInverse (same as P_basic matrix_basic#17) |
| #4 | `moorePenroseInverse_mul_left_of_hasOrthonormalCols` | `moorePenroseInverse_mul_of_hasOrthonormalCols` | |
| #5 | `exists_not_isUnit_add_specNorm_eq_inv_specNorm_inv` (DistanceToSingularity) | `exists_specNorm_eq_not_isUnit_add` | keeper already tagged; Gastinel–Kahan prose + GVL §2.6.2 added |
| #6 | `isUnit_add_of_specNorm_inv_mul_lt_one` | `isUnit_add_of_specNorm_lt`, `isUnit_add_of_specNorm_inv_mul_specNorm_lt_one` | the Gastinel–Kahan wording and its sources (GVL Thm 2.6.2 cor., Higham Thm 6.5) went onto the contrapositive `inv_specNorm_inv_le_specNorm_of_not_isUnit_add`, which already carries `condition-number-def (partial)` |
| #7 | `specNorm_inv_add_le_of_mul_lt_one` | `specNorm_inv_add_le_of_specNorm_inv_mul_specNorm_lt_one` | |
| #8 | Mathlib `Matrix.inv_sub_inv` | `inv_sub_inv_eq_neg_inv_mul_sub_mul_inv`, `inv_add_sub_inv_eq` | `specNorm_inv_add_sub_inv_le`, `frobNorm_inv_add_sub_inv_le` now `rw [Matrix.inv_sub_inv (iff_of_true hAE hA), sub_add_cancel_left, Matrix.mul_neg, Matrix.neg_mul, …]` |
| #9–#12 | `sqrt_pinv_solution_sub_div_le`, `sqrt_pinv_residual_sub_div_le` (LeastSquaresCoordinateBounds), `exists_pos_forall_sqrt_pinv_fit_sub_div_le`, `exists_pos_forall_sqrt_pinv_solution_sub_div_le` (LeastSquaresPurePerturbation) | the four Conditioning wrappers | `least-squares-perturbation (partial)` tags and the TB/Higham/Wedin/GVL citations moved; keepers not renamed |
| #13 | Conditioning's coordinate trio | `LinearSystemPerturbation.lean` (file deleted: `norm_sub_div_norm_le_conditionNumber_mul_residual`, `norm_perturbation_div_norm_le_conditionNumber`, `norm_toEuclideanCLM_apply_le`) | the **non-partial** `atlas: linear-system-perturbation` was the only one making the result `proved`, so `linear_system_perturbation` (same name) is restated in Conditioning as the coordinate bundle (joint bound ∧ a posteriori bound) and keeps the full tag. `toEuclideanCLM_inv_apply_apply` moved verbatim to its only user, MapConditioning |
| #14 | `norm_toEuclideanLin_apply_le` (LeastSquaresGeometry) | `norm_toEuclideanCLM_apply_le` | MapConditioning uses `norm_toEuclideanLin_apply_le A⁻¹ _` (defeq); imports ConditionNumber + LeastSquaresGeometry instead of the deleted file |
| #15–#17 | `specNorm_moorePenroseInverse_sub_le_goldenRatio_max_sq`, `…_goldenRatio_mul_of_rank_eq`, `specNorm_sub_columnProjector_le_min_pinv_mul_specNorm` | the three `A + E` wrappers in InversePerturbation | keepers already tagged; Wedin 1973 / Stewart–Sun Thm III.3.8 citations added |
| #18 | `moorePenroseInverse_sub_eq` (PseudoinverseDifference) | `moorePenroseInverse_add_sub_moorePenroseInverse`, `IsMoorePenroseInverse.sub_eq`, `IsMoorePenroseInverse.transpose_mul_one_sub_mul_eq_zero`, `IsMoorePenroseInverse.one_sub_inv_mul_mul_transpose_eq_zero` | `specNorm_moorePenroseInverse_add_sub_le` reproved from `moorePenroseInverse_sub_eq A (A + E)` + `add_sub_cancel_left` |
| #19 | `IsMoorePenroseInverse.specNorm_one_sub_mul_le` | `specNorm_complement_columnProjector_le_one` | LeastSquaresPerturbation |
| #20 | `specNorm_moorePenroseInverse_le_div_of_rank_eq` (PseudoinverseNormControl) | Fin-only `specNorm_moorePenroseInverse_add_le_of_rank_eq` | keeper already tagged |
| #24 | `exists_eq_mul_transpose_of_posSemidef` (Cholesky) | `exists_cholesky_of_posSemidef`, `choleskyExtend`, `isLowerTriangular_choleskyExtend`, `choleskyExtend_diag_nonneg`, `sqrt_pivot_mul_div_eq`, `choleskyExtend_mul_transpose` | CholeskySemidefinite now only holds `exists_cholesky_of_posSemidef_fintype`, proved by reindexing the keeper; imports Cholesky only |
| #25 | `IsCholesky.unique` | `cholesky_factor_unique` | `existsUnique_cholesky_of_posDef` uses `IsCholesky.unique ⟨…, hMFactor.symm⟩ ⟨…, hFactor.symm⟩`; the QRConsequences use disappeared with `qr_pair_unique` |
| #26 | `det_eq_prod_sq_diag_of_cholesky` (CholeskyDefinite) | `IsCholesky.det_eq_prod_sq` | |
| #30–#32 | `IsQR` **generalised** (see below); `IsQR.eq_of_diag_pos`; `exists_isQR` | `qr_pair_unique`, `exists_qr` (restated as `exists_isQR` in QRExistence: `∃ Q R, IsQR A Q R ∧ ∀ i, 0 ≤ R i i`), old Fin `exists_isQR` | `exists_isQR_of_isUnit` moved to QRExistence and generalised. Users retargeted: QRConsequences, QRDecomposition, QRCompletion, MaximumVolumeQR |
| #31 | `transpose_mul_self_eq_of_qr` kept (finding's option 2), moved verbatim to QR.lean; `IsQR.transpose_mul_self_eq` is now its one-line corollary | — | three keepers in QRConsequences (`isUnit_of_qr_of_rank_eq_card`, `toEuclideanLin_singularValues_eq_of_qr`, the projector lemma) have no triangularity hypothesis, so the unbundled identity is the more general fact |
| (qr tag remark) | `qr_decomposition` restated in the canonical form (`IsQR A Q R ∧ …`; uniqueness clause `IsQR A Q' R' → (∀ i, 0 < R' i i) → …`) and keeps the full `qr-decomposition` tag; its docstring names `exists_isQR` as the existence part | — | `exists_isQR` keeps its `(partial)` tag like the other components |
| #38 | `posDef_matrixExp_and_matrixLog_matrixExp` **generalised** to `{d : Type*} [Fintype d] [DecidableEq d]` (proof unchanged: it never used `Fin`) | `posDef_matrixExp_and_matrixLog_matrixExp_finite` (Probability/…/LiebReindex) | uses renamed in ConditionalLiebPredictable, ConditionalCgf, ConditionalLieb, TraceIntegrability |
| #39 | `traceExp_le_traceExp` (Inequalities/TraceExpMonotone, file owned by P_norms; generalisation assigned to me) **generalised** to any `[Fintype d] [DecidableEq d]`, `[NeZero d]` dropped; needed `relativeEntropy_nonneg` and `generalized_klein` (OperatorTheory) generalised the same way (bodies unchanged) | `traceExp_le_traceExp_finite` (Probability/…/TraceExpBounds) | uses renamed in TraceIntegrability, TracePotentialStep, TracePotentialCrossing, TraceExpBounds; callers pass `A ≤ B`, accepted for `LoewnerLE A B` by defeq |
| #42 | Mathlib `CFC.log_monotoneOn` | `matrixLog_le_matrixLog`; file `OperatorTheory/LogOperatorMonotone.lean` deleted | Probability users BernsteinMgfCgf, ChernoffMgfCgf: `have h : LoewnerLE (matrixLog X) (matrixLog Y) := CFC.log_monotoneOn hX.isStrictlyPositive hY.isStrictlyPositive h`, import OperatorTheory.Basic + Mathlib `…ExpLog.Order`. Its full `operator-monotone-convex` tag is dropped (Mathlib fact); other full tags of that result remain (`relativeEntropy`, `OperatorConvexOn`, …) |
| #43 (step 1) | bridge `matrixLog_eq_log : matrixLog A = CFC.log A := rfl` (Functions/ExpLog) | — | see "Not done" for the retirement |
| #44 | Mathlib `cfc` | def `matrixFunction` (OperatorTheory/Basic) | 9 files in Functions/OperatorTheory; lemmas renamed `matrixFunction_fromBlocks` → `cfc_fromBlocks`, `matrixFunction_sqrt_identities` → `cfc_sqrt_identities`, `OperatorConvexOn.matrixFunction_conjTranspose_mul_mul_le` → `OperatorConvexOn.cfc_conjTranspose_mul_mul_le`. Its full `matrix-calculus-def` tag is dropped (Mathlib definition); the other full tags of that result remain |
| (brief) | `rayleighQuotient_toEuclideanCLM_eq` (Spectral/PowerRayleigh) | `rayleighQuotient_toEuclideanCLM_eq_quadForm_div` (EigenvalueResidualToolkit, unused) | same statement, `rayleighQuotient` unfolds to `quadForm A x / (x ⬝ᵥ x)` |

## Already done / no action

- matrix_pert#22: `eigenvalues₀_add_le_add_eigenvalues₀_zero` is already the one-line corollary of `eigenvalues₀_add_le` (finding's option 2); kept for its tag and the toolkit.
- matrix_pert#33 (F2c), #37 (F2a), #40 (F2c): already executed in phase 1.

## Skipped (owned by other agents, same finding in their task file)

- matrix_pert#21 `frobSq_eq_sum_eigenvalues_sq` (Estimation/Trace/HutchinsonTail) = P_krylov krylov#0.
- matrix_pert#41 `mul_pow_eq_pow_mul_of_mul_eq` (Krylov/Processes/Bidiagonalization) = P_krylov krylov#2.
- matrix_pert#27 `sum_complexCholeskyPivotProbability_mul_trace_step_eq_all` (LowRank) = P_randnla randnla#3.
  Left for the file owners to avoid concurrent edits; none of the three has a user outside its own file.

## Not done: retiring `matrixLog` (matrix_pert#43, step 2)

The `rfl` bridge is in place. Full replacement was not done: 118 occurrences in 30 files, 20 of them
P_prob's Probability files (under concurrent restructuring, probability#36), and the replacement is
not mechanical: `CFC.log` needs a `NormedRing`/`NormedAlgebra ℝ` instance on `Matrix d d ℂ`, which
exists only under a scoped norm (`open scoped Matrix.Norms.L2Operator`), whereas `matrixLog`/`cfc`
need none. Files without that scope (or with a different scoped norm) would fail or produce
instance-mismatched terms. Suggested follow-up (coordinator or P_prob): sed `\bmatrixLog\b` →
`CFC.log` file by file, adding `open scoped Matrix.Norms.L2Operator` where missing, then delete the def.

## Generalisations

- `IsQR` (Factorizations/QR): column index `Fin n` → `{n : Type*} [Fintype n] [LinearOrder n]`; with it
  the whole `IsQR` namespace, `pinvL_eq_of_isQR`, `moorePenroseInverse_eq_of_isQR`,
  `IsQR.mul_transpose_eq`, `IsQR.eq_of_diag_pos`. `IsFullQR` stays on `Fin` (trapezoidal shape).
- `exists_isQR`, `exists_isQR_of_isUnit`: any `Fintype` rows, ordered `Fintype` columns, `|n| ≤ |m|`.
- `posDef_matrixExp_and_matrixLog_matrixExp`, `traceExp_le_traceExp`, `relativeEntropy_nonneg`,
  `generalized_klein`: `Fin d` (+`[NeZero d]`) → `{d : Type*} [Fintype d] [DecidableEq d]`.

## Files created / deleted

- Deleted: `NLAlib/Matrix/Perturbation/LinearSystemPerturbation.lean`,
  `NLAlib/Matrix/OperatorTheory/LogOperatorMonotone.lean` (aggregators regenerated with
  `python3 scripts/reorg.py --gen-aggregators`; `scripts/AuditNewProofs.lean` module list updated).
- No file created.

## Foreign files touched (reference edits)

Subspaces/ObliqueFrameInverse; Inequalities/TraceExpMonotone (the assigned generalisation);
Probability/Concentration/Matrix/{TraceIntegrability, TraceExpBounds, LiebReindex, BernsteinMgfCgf,
ChernoffMgfCgf}; Probability/Concentration/Martingales/{TracePotentialStep, TracePotentialCrossing,
ConditionalLieb, ConditionalLiebPredictable, ConditionalCgf}. In TraceExpBounds and LiebReindex the
`_finite` declarations were deleted (as instructed: P_prob's probability#28/#30 are thereby done).

## Coordinator follow-ups

- Atlas (`sync_atlas.py`): `linear-system-perturbation` formalizations change (bundle
  `linear_system_perturbation` moves module, now coordinate form); `condition-number-def` gains
  `conditionNumber_eq_mul_specNorm_inv`; `least-squares-perturbation` gains the four Coordinate/Pure
  keepers; `operator-monotone-convex` loses `matrixLog_le_matrixLog` (cite `CFC.log_monotoneOn` under
  `mathlib_prereqs`); `matrix-calculus-def` loses `matrixFunction` (cite `cfc`).
- `docs/TroppMatrixConcentration.md` still mentions `matrixFunction_*` names.
- InversePerturbation still imports `Matrix.Spectral.Weyl`, no longer needed by its own content
  (kept to avoid breaking transitive users).

## Compilation

`lake build` of every module I edited plus all their direct dependants (79 modules, list computed
from the import graph), then `Krylov.Spectral.QRAlgorithm`, `Factorizations.CholeskyToolkit` and the
`Matrix.OperatorTheory`/`Matrix.Functions` aggregators: all build. The only `sorry` warnings are
the pre-existing scaffolds (Cholesky.lean pivoted-Cholesky lemmas, `givensQRQ_invariant`).
`Matrix/Inequalities/BlockStrictContraction` failed once on another agent's in-progress
HaynsworthInertia edit (not a name of mine) and built on retry.

## Summary

All 39 findings handled: 33 executed (counting the bridge for #43), 3 already done in phase 1 or
already in the requested form, 3 left to the owning agents (P_krylov, P_randnla) who carry the same
finding. Two files were deleted. `IsQR` and four Tropp-port theorems were generalised from `Fin` to
`Fintype`. `matrixFunction` and `matrixLog_le_matrixLog` were retired in favour of Mathlib.
Retiring `matrixLog` is left as a follow-up because of the scoped-norm problem described above.
