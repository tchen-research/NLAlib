# F4 wave 1, fork M2-S (cluster `Matrix/Subspaces`): report

Status: IN PROGRESS. Requests to other owners first (read while the round runs).

## Requests to M1

1. **`Subspaces/ComplexProjectionBounds.lean` is deleted** (D5). Its lemmas were ℂ copies of
   𝕜 lemmas; use these instead (all over `[RCLike 𝕜]`, norms spelled `specNorm`/`frobSq`):
   - `norm_le_one_of_isHermitian_of_isIdempotentElem` → `Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem` (`Norms/Core`).
   - `norm_mul_left_of_conjTranspose_mul_eq_one` → `specNorm_mul_left_of_conjTranspose_mul_self` (`Norms/SpectralNormBounds`, M1's; takes `Pᴴ * P = 1`, i.e. `hP : HasOrthonormalCols P` by defeq).
   - `norm_mul_conjTranspose_right_of_conjTranspose_mul_eq_one` → `specNorm_mul_conjTranspose_right_of_conjTranspose_mul_self`.
   - `norm_add_sq_le_of_mul_conjTranspose_eq_zero` → `specNorm_add_sq_le_of_mul_conjTranspose_eq_zero` (`Norms/Core`).
   - `frobenius_norm_sq_eq_re_trace_mul_conjTranspose : ‖A‖² = (A Aᴴ).trace.re` →
     `frobSq_eq_re_trace_mul_conjTranspose` (`Subspaces/ProjectorBlocks.lean`, 𝕜:
     `frobSq A = RCLike.re (A * Aᴴ).trace`); with `frobNorm_eq_norm`/`frobSq = frobNorm ^ 2`
     under `open scoped Matrix.Norms.Frobenius in` if the `‖·‖` form is needed in a proof
     (used by `Spectral/NormalBlocks`).
   - `frobenius_norm_sq_mul_left_of_conjTranspose_mul_eq_one` → `frobSq_mul_left_of_orthonormal` (`Norms/Frobenius`) (used by `Spectral/SchurFrobenius`, `Perturbation/HoffmanWielandtNormal`).
   - `frobenius_norm_sq_mul_conjTranspose_right_of_conjTranspose_mul_eq_one` → `frobSq_mul_right_of_orthonormal` (same files).
   - `frobenius_norm_add_sq_eq_of_mul_conjTranspose_eq_zero` → `frobSq_add_of_mul_conjTranspose_eq_zero` (`Subspaces/ProjectorBlocks.lean`).
   - `frobenius_norm_sq_eq_left_projection_add_residual` / `..._right_...` →
     `frobSq_projector_mul_add_complement` / `frobSq_mul_projector_add_complement` (`Subspaces/ProjectorBlocks.lean`, 𝕜, `IsHermitian`).
   - `norm_one_sub_complexColumnProjector_le`, `norm_sub_complexColumnProjector_mul_le`,
     `frobenius_norm_sub_complexColumnProjector_mul_sq_le` → `specNorm_one_sub_rangeProjector_le_one`,
     `specNorm_sub_rangeProjector_mul_le`, `frobSq_sub_rangeProjector_mul_le` (`Subspaces/RangeProjector.lean`).
   Imports to change: `Spectral/NormalBlocks`, `Spectral/SchurFrobenius`,
   `Perturbation/HoffmanWielandtNormal` (`import NLAlib.Matrix.Subspaces.ComplexProjectionBounds` →
   `NLAlib.Matrix.Subspaces.ProjectorBlocks` and/or `NLAlib.Matrix.Norms.Frobenius`).
2. **`singularValues_conjTranspose` over 𝕜** (`Spectral/SingularValueInvariance.lean`, now ℝ-only
   `singularValues_transpose`): the proof generalises verbatim (`exists_isSVD`, `h.conjTranspose_eq`,
   `singularValues_eq_of_eq_mul_rectDiag_mul`). Likewise `singularValues_isometry_mul`,
   `singularValues_mul_isometry_conjTranspose` (was `_transpose`), `singularValues_mul_unitary`
   (was `_orthogonal`) over 𝕜 with `HasOrthonormalCols`. M2-S proves private 𝕜 copies in
   `Subspaces/ObliqueCanonicalSpectrum.lean` meanwhile; delete them once M1's exist (noted below).
3. `principalAnglesFintype` → `principalAngles (P Q : Matrix m n 𝕜) : Fin (card n) → ℝ :=
   fun i => arccos (singularValues (Pᴴ * Q) i)` (no reindex). Statements in
   `Perturbation/DavisKahan*`, `Wedin*`, `PopulationTraceGap` that use `sinePrincipalAngles` keep
   the name; lemmas about the overlap singular values lose the
   `(Pᵀ*Q).reindex (equivFin n) (equivFin n)` spelling (`singularValues (Pᴴ * Q) i`).
4. `Subspaces/CSToolkit`, `ComplexCSToolkit`, `PrincipalAngleToolkit` are deleted (bundles);
   component theorems carry the atlas tags.

(Report body filled in at the end.)
