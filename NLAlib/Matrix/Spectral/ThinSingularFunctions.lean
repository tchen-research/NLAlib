import NLAlib.Matrix.Spectral.ThinSVD
import NLAlib.Matrix.Norms.SpectralNormBounds

/-! # Scalar operations in fixed thin singular directions

Real diagonal coefficients may have any signs. The algebraic identities thus
apply to polynomial polar iterations even when intermediate scalar values
are not ordered singular values. Source: Horn–Johnson, §7.3.
-/
noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- A real diagonal coefficient function between two fixed singular frames. -/
def thinSingularMatrix (U : Matrix m r 𝕜) (V : Matrix n r 𝕜) (f : r → ℝ) : Matrix m n 𝕜 :=
  U * Matrix.diagonal (fun i => (f i : 𝕜)) * Vᴴ

omit [Fintype m] [Fintype n] in
/-- Adjoint reverses the singular frames and leaves real coefficients unchanged. -/
theorem thinSingularMatrix_conjTranspose (U : Matrix m r 𝕜) (V : Matrix n r 𝕜)
    (f : r → ℝ) : (thinSingularMatrix U V f)ᴴ = thinSingularMatrix V U f := by
  have hd : (Matrix.diagonal fun i => (f i : 𝕜))ᴴ = Matrix.diagonal (fun i => (f i : 𝕜)) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [Matrix.conjTranspose_apply]
    · simp [Matrix.conjTranspose_apply, h, Ne.symm h]
  simp only [thinSingularMatrix, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hd, Matrix.mul_assoc]

omit [Fintype m] in
/-- Multiplication cancels a shared orthonormal singular frame. -/
theorem thinSingularMatrix_mul {p : Type*} [Fintype p]
    (U : Matrix m r 𝕜) (V : Matrix n r 𝕜) (W : Matrix p r 𝕜)
    (hV : HasOrthonormalCols V) (f g : r → ℝ) :
    thinSingularMatrix U V f * thinSingularMatrix V W g =
      thinSingularMatrix U W (fun i => f i * g i) := by
  have he : thinSingularMatrix U V f * thinSingularMatrix V W g =
      U * (Matrix.diagonal (fun i => (f i : 𝕜)) *
        Matrix.diagonal (fun i => (g i : 𝕜))) * Wᴴ := by
    simp only [thinSingularMatrix, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V (Matrix.diagonal _ * Wᴴ),
      hV.conjTranspose_mul_self, Matrix.one_mul]
  rw [he, Matrix.diagonal_mul_diagonal]
  simp only [thinSingularMatrix, RCLike.ofReal_mul]

omit [Fintype m] [Fintype n] in
/-- Real linear combinations operate coordinatewise in fixed singular directions. -/
theorem thinSingularMatrix_add (U : Matrix m r 𝕜) (V : Matrix n r 𝕜)
    (f g : r → ℝ) :
    thinSingularMatrix U V f + thinSingularMatrix U V g =
      thinSingularMatrix U V (fun i => f i + g i) := by
  have hd : (Matrix.diagonal fun i => ((f i + g i : ℝ) : 𝕜)) =
      Matrix.diagonal (fun i => (f i : 𝕜)) + Matrix.diagonal (fun i => (g i : 𝕜)) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [thinSingularMatrix, thinSingularMatrix, thinSingularMatrix, hd,
    Matrix.mul_add, Matrix.add_mul]

omit [Fintype m] [Fintype n] in
/-- A real scalar acts on the coefficient function. -/
theorem thinSingularMatrix_smul (U : Matrix m r 𝕜) (V : Matrix n r 𝕜)
    (a : ℝ) (f : r → ℝ) :
    a • thinSingularMatrix U V f = thinSingularMatrix U V (fun i => a * f i) := by
  have hd : (Matrix.diagonal fun i => ((a * f i : ℝ) : 𝕜)) =
      a • Matrix.diagonal (fun i => (f i : 𝕜)) := by
    ext i j
    by_cases h : i = j <;> simp [h, Algebra.smul_def]
  rw [thinSingularMatrix, thinSingularMatrix, hd, Matrix.mul_smul, Matrix.smul_mul]

/-- The Gram matrix is diagonal in the right singular frame. -/
theorem thinSingularMatrix_gram (U : Matrix m r 𝕜) (V : Matrix n r 𝕜)
    (hU : HasOrthonormalCols U) (f : r → ℝ) :
    (thinSingularMatrix U V f)ᴴ * thinSingularMatrix U V f =
      thinSingularMatrix V V (fun i => f i ^ 2) := by
  rw [thinSingularMatrix_conjTranspose, thinSingularMatrix_mul V U V hU]
  simp only [pow_two]

open scoped Matrix.Norms.L2Operator in
/-- The exact spectral norm is the supremum norm of the real coefficients,
including the empty singular block. -/
theorem specNorm_thinSingularMatrix [DecidableEq m] [DecidableEq n]
    (U : Matrix m r 𝕜) (V : Matrix n r 𝕜)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (f : r → ℝ) :
    specNorm (thinSingularMatrix U V f) = ‖f‖ := by
  rw [thinSingularMatrix, specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hV,
    specNorm_mul_left_of_hasOrthonormalCols hU, specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr (fun i => by
      simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using norm_le_pi_norm f i)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => by
      simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using
        norm_le_pi_norm (fun i => (f i : 𝕜)) i)

omit [Fintype m] [Fintype n] in
/-- The difference of two coefficient functions stays in the same frames. -/
theorem thinSingularMatrix_sub (U : Matrix m r 𝕜) (V : Matrix n r 𝕜)
    (f g : r → ℝ) :
    thinSingularMatrix U V f - thinSingularMatrix U V g =
      thinSingularMatrix U V (fun i => f i - g i) := by
  have hd : (Matrix.diagonal fun i => ((f i - g i : ℝ) : 𝕜)) =
      Matrix.diagonal (fun i => (f i : 𝕜)) - Matrix.diagonal (fun i => (g i : 𝕜)) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [thinSingularMatrix, thinSingularMatrix, thinSingularMatrix, hd,
    Matrix.mul_sub, Matrix.sub_mul]

end NLAlib
