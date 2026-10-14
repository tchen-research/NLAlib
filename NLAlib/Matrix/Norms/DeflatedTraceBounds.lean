import NLAlib.Matrix.Norms.EntryBounds
import NLAlib.Matrix.Subspaces.Projections
import NLAlib.Matrix.Basic.QuadForm

/-!
# Uniform bounds for orthogonal trace deflation

An orthonormal compression and its complementary quadratic form have a bound independent
of the choice of frame. This is the deterministic domination (T2) used by
`hutchpp-unbiased` and `xtrace-unbiased`; it holds for nonsymmetric real matrices and empty
row or column types.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- The absolute trace of a real square matrix is bounded by its dimension times its
spectral norm. This includes empty matrices. -/
theorem abs_trace_le_card_mul_specNorm (A : Matrix n n ℝ) :
    |A.trace| ≤ Fintype.card n * specNorm A := by
  calc |A.trace| ≤ ∑ i, |A i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, specNorm A := Finset.sum_le_sum fun i _ => abs_apply_le_specNorm A i i
    _ = _ := by simp

/-- Orthonormal compression cannot increase the spectral norm, even for nonsymmetric
matrices. This bounds the deterministic trace correction in deflated trace estimation. -/
theorem specNorm_conjTranspose_mul_mul_le_of_hasOrthonormalCols
    {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) (A : Matrix n n ℝ) :
    specNorm (Qᴴ * A * Q) ≤ specNorm A := by
  have hQnorm := specNorm_le_one_of_orthonormal hQ.conjTranspose_mul_self
  have hQstar : specNorm Qᴴ ≤ 1 := by simpa only [specNorm_conjTranspose] using hQnorm
  calc specNorm (Qᴴ * A * Q) ≤ specNorm (Qᴴ * A) * specNorm Q := specNorm_mul_le _ _
    _ ≤ (1 * specNorm A) * 1 := by
      apply mul_le_mul
      · exact (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right hQstar (specNorm_nonneg A))
      · exact hQnorm
      · exact specNorm_nonneg _
      · exact mul_nonneg zero_le_one (specNorm_nonneg A)
    _ = specNorm A := by ring

/-- The complementary two-sided orthogonal compression cannot increase the spectral
norm. It bounds the residual quadratic form uniformly in the orthonormal frame. -/
theorem specNorm_one_sub_mul_conjTranspose_mul_mul_one_sub_le
    {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) (A : Matrix n n ℝ) :
    specNorm ((1 - Q * Qᴴ) * A * (1 - Q * Qᴴ)) ≤ specNorm A := by
  have hleft (B : Matrix n n ℝ) : specNorm ((1 - Q * Qᴴ) * B) ≤ specNorm B := by
    simpa only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc] using
      specNorm_sub_mul_conjTranspose_mul_le hQ.conjTranspose_mul_self B
  have hright : specNorm (A * (1 - Q * Qᴴ)) ≤ specNorm A := by
    calc
      specNorm (A * (1 - Q * Qᴴ)) = specNorm ((1 - Q * Qᴴ) * Aᴴ) := by
        rw [← specNorm_conjTranspose (A * (1 - Q * Qᴴ)), Matrix.conjTranspose_mul,
          Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
      _ ≤ specNorm Aᴴ := hleft _
      _ = specNorm A := specNorm_conjTranspose _
  simpa only [Matrix.mul_assoc] using (hleft (A * (1 - Q * Qᴴ))).trans hright

/-- Uniform domination for a compressed trace plus the complementary quadratic form:
`|tr(Qᵀ A Q) + wᵀ(I-QQᵀ)A(I-QQᵀ)w| ≤ ‖A‖₂(d + ‖w‖₂²)`.
Source: supplied operator derivations, (T2). The matrix need not be symmetric and empty
frames and zero-dimensional matrices are included. Helper for `hutchpp-unbiased` and
`xtrace-unbiased`. -/
theorem abs_trace_compression_add_quadForm_residual_le
    (A : Matrix n n ℝ) {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) (w : n → ℝ) :
    |(Qᵀ * A * Q).trace + quadForm ((1 - Q * Qᵀ) * A * (1 - Q * Qᵀ)) w| ≤
      specNorm A * (Fintype.card n + ‖WithLp.toLp 2 w‖ ^ 2) := by
  have hcompression : |(Qᵀ * A * Q).trace| ≤ Fintype.card n * specNorm A := by
    calc |(Qᵀ * A * Q).trace| ≤ Fintype.card r * specNorm (Qᵀ * A * Q) :=
        abs_trace_le_card_mul_specNorm _
      _ ≤ Fintype.card n * specNorm A := by
        apply mul_le_mul
        · exact_mod_cast card_le_card_of_hasOrthonormalCols hQ
        · exact specNorm_conjTranspose_mul_mul_le_of_hasOrthonormalCols hQ A
        · exact specNorm_nonneg _
        · positivity
  have hresidual : |quadForm ((1 - Q * Qᵀ) * A * (1 - Q * Qᵀ)) w| ≤
      specNorm A * ‖WithLp.toLp 2 w‖ ^ 2 := by
    calc |quadForm ((1 - Q * Qᵀ) * A * (1 - Q * Qᵀ)) w| ≤
        specNorm ((1 - Q * Qᵀ) * A * (1 - Q * Qᵀ)) * (w ⬝ᵥ w) :=
          abs_dotProduct_mulVec_le_specNorm _ _
      _ ≤ specNorm A * ‖WithLp.toLp 2 w‖ ^ 2 := by
        rw [norm_toLp_sq_eq_dotProduct_self]
        exact mul_le_mul_of_nonneg_right
          (specNorm_one_sub_mul_conjTranspose_mul_mul_one_sub_le hQ A)
          (dotProduct_self_nonneg w)
  exact (abs_add_le _ _).trans ((add_le_add hcompression hresidual).trans_eq (by ring))

end NLAlib
