import NLAlib.Matrix.Norms.Core

/-!
# Stability of orthogonal conjugation in Frobenius norm

Moving an orthonormal coordinate frame by `E` changes a fixed square matrix's
representation by at most `2 ‖A‖₂ ‖E‖F`. This applies over real or complex scalars.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Frobenius perturbation bound for two orthonormal coordinate frames. -/
theorem frobNorm_conjTranspose_mul_mul_sub_le (A : Matrix n n 𝕜)
    {U V : Matrix n n 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    frobNorm (Uᴴ * A * U - Vᴴ * A * V) ≤ 2 * specNorm A * frobNorm (U - V) := by
  have he : Uᴴ * A * U - Vᴴ * A * V =
      Uᴴ * (A * (U - V)) + (U - V)ᴴ * (A * V) := by
    simp only [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
    abel
  have hUt : specNorm Uᴴ ≤ 1 := by
    rw [specNorm_conjTranspose]
    exact specNorm_le_one_of_orthonormal hU
  have hAv : specNorm (A * V) ≤ specNorm A := by
    exact (specNorm_mul_le _ _).trans (by
      nlinarith [specNorm_le_one_of_orthonormal hV, specNorm_nonneg A])
  rw [he]
  calc
    _ ≤ frobNorm (Uᴴ * (A * (U - V))) + frobNorm ((U - V)ᴴ * (A * V)) := frobNorm_add_le _ _
    _ ≤ specNorm Uᴴ * frobNorm (A * (U - V)) + frobNorm (U - V)ᴴ * specNorm (A * V) :=
      add_le_add (frobNorm_mul_le_specNorm_mul_frobNorm _ _) (frobNorm_mul_le_frobNorm_mul_specNorm _ _)
    _ ≤ frobNorm (A * (U - V)) + frobNorm (U - V) * specNorm A := by
      rw [frobNorm_conjTranspose]
      exact add_le_add (by nlinarith [frobNorm_nonneg (A * (U - V))])
        (mul_le_mul_of_nonneg_left hAv (frobNorm_nonneg _))
    _ ≤ _ := by
      nlinarith [frobNorm_mul_le_specNorm_mul_frobNorm A (U - V)]

end NLAlib
