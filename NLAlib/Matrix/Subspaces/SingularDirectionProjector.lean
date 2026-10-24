/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Subspaces.OrthogonalProducts

/-! # Projectors onto selected singular-frame coordinates

A Boolean selection of columns of an orthonormal frame is represented by its
Gram projector. The same algebra supports hard thresholding, leading singular
projectors, and streaming SVD shrinkage without importing optimization theory.
Source: orthogonal projection in singular coordinates, Horn–Johnson (2013), §2.6.
-/

noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib
variable {𝕜 m : Type*} [RCLike 𝕜] [Fintype m] [DecidableEq m]

/-- Select a Boolean mask of directions of a full left singular frame. This is an
orthogonal projector when the frame is unitary; no zero-padded frame is claimed orthonormal. -/
def singularDirectionProjector {p : ℕ} (U : Matrix m (Fin p) 𝕜) (keep : Fin p → Bool) :
    Matrix m m 𝕜 := U * Matrix.diagonal (fun i => if keep i then (1 : 𝕜) else 0) * Uᴴ

omit [DecidableEq m] [Fintype m] in
/-- Every selected-coordinate Gram projector is Hermitian. -/
theorem singularDirectionProjector_isHermitian {p : ℕ}
    (U : Matrix m (Fin p) 𝕜) (keep : Fin p → Bool) :
    (singularDirectionProjector U keep).IsHermitian := by
  exact Matrix.isHermitian_mul_mul_conjTranspose U
    (Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      ext i
      simp only [Pi.star_apply]
      split_ifs <;> simp))

omit [DecidableEq m] in
/-- Selecting columns of an orthonormal frame produces an idempotent projector. -/
theorem HasOrthonormalCols.isIdempotentElem_singularDirectionProjector {p : ℕ}
    {U : Matrix m (Fin p) 𝕜} (hU : HasOrthonormalCols U) (keep : Fin p → Bool) :
    IsIdempotentElem (singularDirectionProjector U keep) := by
  let D : Matrix (Fin p) (Fin p) 𝕜 := Matrix.diagonal (fun i => if keep i then 1 else 0)
  have hD : D * D = D := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  change (U * D * Uᴴ) * (U * D * Uᴴ) = U * D * Uᴴ
  calc
    _ = U * (D * (Uᴴ * U) * D) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU.conjTranspose_mul_self, Matrix.mul_one, hD]

omit [DecidableEq m] in
/-- In frame coordinates, the selected projector is the diagonal Boolean mask. -/
theorem HasOrthonormalCols.conjTranspose_mul_singularDirectionProjector_mul {p : ℕ}
    {U : Matrix m (Fin p) 𝕜} (hU : HasOrthonormalCols U) (keep : Fin p → Bool) :
    Uᴴ * singularDirectionProjector U keep * U =
      Matrix.diagonal (fun i => if keep i then 1 else 0) := by
  let D : Matrix (Fin p) (Fin p) 𝕜 := Matrix.diagonal (fun i => if keep i then 1 else 0)
  change Uᴴ * (U * D * Uᴴ) * U = D
  calc
    _ = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU.conjTranspose_mul_self, Matrix.one_mul, Matrix.mul_one]

end NLAlib
