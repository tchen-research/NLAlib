import NLAlib.Matrix.Structured.RectangularCoefficientBlocks
import NLAlib.Matrix.Structured.CoefficientBlockBounds
import NLAlib.Matrix.Norms.Complexification
import NLAlib.Matrix.Norms.Dilation
import NLAlib.Matrix.Norms.BlockDiagonalBounds

/-!
# Variance and covariance parameters of a real rectangular dilation

The Hermitian dilation preserves the variance maximum. On the real coefficient
space its vectorization is a Frobenius isometry times `sqrt 2`, which gives the
exact covariance factor used by the strong chaos estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib

variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]
  [DecidableEq ι] [DecidableEq m] [DecidableEq n]

/-- Complex Hermitian dilations of a real rectangular coefficient family. -/
def realCoefficientDilation (B : ι → Matrix m n ℝ) (i : ι) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ := dilation ((B i).map Complex.ofReal)

/-- Real coefficient dilations are Hermitian. -/
theorem isHermitian_realCoefficientDilation (B : ι → Matrix m n ℝ) (i : ι) :
    (realCoefficientDilation B i).IsHermitian := isHermitian_dilation _

/-- The actual variance of the dilated family is the block diagonal matrix of
the original row and column variances. -/
theorem coefficientVariance_realCoefficientDilation (B : ι → Matrix m n ℝ) :
    coefficientVariance (realCoefficientDilation B) =
      Matrix.fromBlocks ((∑ i, B i * (B i)ᴴ).map Complex.ofReal) 0 0
        ((∑ i, (B i)ᴴ * B i).map Complex.ofReal) := by
  have h (i : ι) : realCoefficientDilation B i * realCoefficientDilation B i =
      Matrix.fromBlocks (((B i) * (B i)ᴴ).map Complex.ofReal) 0 0
        (((B i)ᴴ * B i).map Complex.ofReal) := by
    rw [realCoefficientDilation, ← sq, dilation_sq]
    ext (a | a) (b | b) <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum,
        Complex.ofReal_mul]
  unfold coefficientVariance
  simp_rw [h]
  ext (a | a) (b | b) <;> simp [Matrix.sum_apply, Complex.ofReal_sum]

/-- The square-root variance parameter of a real rectangular dilation is
bounded by its two row/column block norms. -/
theorem sqrt_specNorm_variance_realCoefficientDilation_le
    (B : ι → Matrix m n ℝ) :
    Real.sqrt (specNorm (coefficientVariance (realCoefficientDilation B))) ≤
      specNorm (coefficientRow B) + specNorm (coefficientColumn B) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (specNorm_nonneg _) (specNorm_nonneg _), ?_⟩
  rw [coefficientVariance_realCoefficientDilation]
  apply (specNorm_fromBlocks_diagonal_le _ _).trans
  have hR : specNorm ((∑ i, B i * (B i)ᴴ).map Complex.ofReal) =
      specNorm (coefficientRow B) ^ 2 := by
    have hm := specNorm_map_ofReal (𝕜 := ℂ) (∑ i, B i * (B i)ᴴ)
    simp only [Complex.coe_algebraMap] at hm
    exact hm.trans (specNorm_coefficientRow_sq B).symm
  have hC : specNorm ((∑ i, (B i)ᴴ * B i).map Complex.ofReal) =
      specNorm (coefficientColumn B) ^ 2 := by
    have hm := specNorm_map_ofReal (𝕜 := ℂ) (∑ i, (B i)ᴴ * B i)
    simp only [Complex.coe_algebraMap] at hm
    exact hm.trans (specNorm_coefficientColumn_sq B).symm
  rw [hR, hC]
  apply max_le <;> nlinarith [specNorm_nonneg (coefficientRow B),
    specNorm_nonneg (coefficientColumn B)]

/-- The Gram matrix of the vectorized dilations is twice the original real
coefficient-row Gram matrix after scalar extension. The real hypothesis is
essential: complex dilation is only real-linear. -/
theorem coefficientVectorization_gram_realCoefficientDilation
    (B : ι → Matrix m n ℝ) :
    (coefficientVectorization (realCoefficientDilation B))ᴴ *
        coefficientVectorization (realCoefficientDilation B) =
      (2 : ℝ) • ((coefficientEntryRows B * (coefficientEntryRows B)ᴴ).map Complex.ofReal) := by
  ext i j
  apply Complex.ext
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, coefficientVectorization,
      realCoefficientDilation, dilation, coefficientEntryRows, Fintype.sum_prod_type,
      Fintype.sum_sum_type, Matrix.smul_apply, Complex.ofReal_sum, Complex.ofReal_mul]
    have hs : (∑ b : n, ∑ a : m, B i a b * B j a b) =
        ∑ a : m, ∑ b : n, B i a b * B j a b := Finset.sum_comm
    linarith
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, coefficientVectorization,
      realCoefficientDilation, dilation, coefficientEntryRows, Fintype.sum_prod_type,
      Fintype.sum_sum_type, Matrix.smul_apply, Complex.ofReal_sum, Complex.ofReal_mul]

open scoped Matrix.Norms.L2Operator in
/-- Dilation multiplies the vectorized coefficient-matrix norm by exactly
`sqrt 2` on real rectangular coefficient families. -/
theorem specNorm_coefficientVectorization_realCoefficientDilation
    (B : ι → Matrix m n ℝ) :
    specNorm (coefficientVectorization (realCoefficientDilation B)) =
      Real.sqrt 2 * specNorm (coefficientEntryRows B) := by
  have hs : specNorm (coefficientVectorization (realCoefficientDilation B)) ^ 2 =
      2 * specNorm (coefficientEntryRows B) ^ 2 := by
    rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self,
      coefficientVectorization_gram_realCoefficientDilation, specNorm_eq_norm,
      norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← specNorm_eq_norm]
    have hm := specNorm_map_ofReal (𝕜 := ℂ)
      (coefficientEntryRows B * (coefficientEntryRows B)ᴴ)
    simp only [Complex.coe_algebraMap] at hm
    rw [hm, specNorm_mul_conjTranspose_self]
  apply (sq_eq_sq₀ (specNorm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (specNorm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact hs

/-- The square-root entry-covariance parameter of the dilated family is exactly
`sqrt 2` times the original real coefficient-entry matrix norm. -/
theorem sqrt_specNorm_covariance_realCoefficientDilation
    (B : ι → Matrix m n ℝ) :
    Real.sqrt (specNorm (coefficientCovariance (realCoefficientDilation B))) =
      Real.sqrt 2 * specNorm (coefficientEntryRows B) := by
  rw [coefficientCovariance, specNorm_mul_conjTranspose_self,
    Real.sqrt_sq (specNorm_nonneg _), specNorm_coefficientVectorization_realCoefficientDilation]

end NLAlib
