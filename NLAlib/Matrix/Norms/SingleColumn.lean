import NLAlib.Matrix.Spectral.SpectralBounds

/-!
# Spectral norm of a single column

The Gram identity identifies the squared Euclidean operator norm of a
one-column real or complex matrix with the vector's squared Euclidean norm. This is the
norm calculation used by the one-column principal-angle bridge.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n]

open scoped Matrix.Norms.L2Operator in
/-- A single column has squared spectral norm equal to the vector's squared Euclidean norm.
Source: the finite-dimensional Gram identity; matrix-toolkit derivations,
Lemma 1.1. This includes the zero vector and an empty row index type. -/
theorem specNorm_sq_replicateCol {𝕜 : Type*} [RCLike 𝕜] (v : n → 𝕜) :
    specNorm (Matrix.replicateCol Unit v) ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 := by
  have hG : (Matrix.replicateCol Unit v)ᴴ * Matrix.replicateCol Unit v =
      Matrix.diagonal (fun _ : Unit => (‖WithLp.toLp 2 v‖ : 𝕜) ^ 2) := by
    ext i j
    cases i
    cases j
    have hinner := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (WithLp.toLp 2 v)
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at hinner
    simpa [Matrix.mul_apply, dotProduct] using hinner
  rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self, hG, specNorm_eq_norm,
    Matrix.l2_opNorm_diagonal]
  simp only [pi_norm_const, norm_pow, RCLike.norm_ofReal, abs_norm]

end NLAlib
