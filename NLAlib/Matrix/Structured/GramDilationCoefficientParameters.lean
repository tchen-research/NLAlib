import NLAlib.Matrix.Structured.RectangularCoefficientBlocks
import NLAlib.Matrix.Structured.CoefficientBlockBounds
import NLAlib.Matrix.Structured.CoefficientBilinearParameters
import NLAlib.Matrix.Norms.BlockDiagonalBounds
import NLAlib.Matrix.Spectral.CStarRectangularDilationComparison

/-! # Complex coefficient parameters of the positive Gram linearization

The actual three-block Hermitian coefficient matrices retain the original
variance maximum and have covariance at most twice the original entry
covariance. Complex conjugation is retained in the vectorized Gram
identity; complex dilation is only real-linear.
Source: arXiv:2406.11453v2, Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

omit [DecidableEq ι] in
/-- Actual bilinear coefficient energy is bounded by the column variance
without a Hermitian hypothesis on the original coefficients. -/
theorem bilinearSquareMass_le_specNorm_sum_conjTranspose_mul_self
    (A : ι → Matrix d d ℂ) :
    bilinearSquareMass A Finset.univ ≤ specNorm (∑ i, (A i)ᴴ * A i) := by
  obtain ⟨v, w, hv, hw, he⟩ := exists_bilinearSquareMass_eq A Finset.univ
  rw [he]
  calc
    _ ≤ ∑ i : ι, ‖WithLp.toLp 2 (A i *ᵥ w.ofLp)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := norm_inner_le_norm (𝕜 := ℂ) v (WithLp.toLp 2 (A i *ᵥ w.ofLp))
      have heq : inner ℂ v (WithLp.toLp 2 (A i *ᵥ w.ofLp)) =
          star v.ofLp ⬝ᵥ (A i *ᵥ w.ofLp) := by
        rw [← WithLp.toLp_ofLp 2 v, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
      rw [heq] at hi
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hi.trans (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hv (norm_nonneg _))) 2
    _ ≤ _ := sum_norm_sq_mulVec_le_specNorm_sum_gram A Finset.univ w hw

/-- The original non-Hermitian source weak scale is bounded by the actual
geometric variance/covariance scale used by quadratic comparison. -/
theorem sqrt_bilinearSquareMass_le_sqrt_rectangular_variance_covariance
    (A : ι → Matrix d d ℂ) :
    Real.sqrt (bilinearSquareMass A Finset.univ) ≤
      Real.sqrt (Real.sqrt (max (specNorm (∑ i, A i * (A i)ᴴ))
        (specNorm (∑ i, (A i)ᴴ * A i))) *
        Real.sqrt (specNorm (coefficientCovariance A))) := by
  have hV := Real.sqrt_le_sqrt
    ((bilinearSquareMass_le_specNorm_sum_conjTranspose_mul_self A).trans (le_max_right (specNorm (∑ i, A i * (A i)ᴴ))
      (specNorm (∑ i, (A i)ᴴ * A i))))
  have hW := Real.sqrt_le_sqrt (bilinearSquareMass_le_specNorm_coefficientCovariance A)
  have hprod := mul_le_mul hV hW (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (bilinearSquareMass_nonneg _ _), Real.sq_sqrt (by positivity)]
  simpa only [← pow_two, Real.sq_sqrt (bilinearSquareMass_nonneg _ _)] using hprod

/-- The literal variable row `[A,0]` in the positive Gram linearization. -/
def gramCoefficientRow (A : Matrix d d ℂ) : Matrix d (d ⊕ d) ℂ :=
  fun a => Sum.elim (A a) 0

/-- The actual Hermitian coefficients on the `3d`-dimensional positive
Gram dilation. The square-root block belongs to the deterministic mean. -/
def gramCoefficientDilation (A : ι → Matrix d d ℂ) (i : ι) :
    Matrix (d ⊕ (d ⊕ d)) (d ⊕ (d ⊕ d)) ℂ := dilation (gramCoefficientRow (A i))

omit [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d] in
/-- The actual three-block coefficient family is Hermitian. -/
theorem isHermitian_gramCoefficientDilation (A : ι → Matrix d d ℂ) (i : ι) :
    (gramCoefficientDilation A i).IsHermitian := isHermitian_dilation _

omit [DecidableEq ι] [DecidableEq d] in
/-- Its literal variance consists of the two original row/column variance
blocks and one zero block. -/
theorem coefficientVariance_gramCoefficientDilation (A : ι → Matrix d d ℂ) :
    coefficientVariance (gramCoefficientDilation A) =
      Matrix.fromBlocks (∑ i, A i * (A i)ᴴ) 0 0
        (Matrix.fromBlocks (∑ i, (A i)ᴴ * A i) 0 0 0) := by
  ext (a | (a | a)) (b | (b | b)) <;>
    simp [coefficientVariance, gramCoefficientDilation, gramCoefficientRow, dilation,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type, Matrix.sum_apply]

omit [DecidableEq ι] in
/-- The actual Hermitian variance is bounded by precisely the original
non-Hermitian row/column variance maximum. -/
theorem specNorm_coefficientVariance_gramCoefficientDilation_le
    (A : ι → Matrix d d ℂ) :
    specNorm (coefficientVariance (gramCoefficientDilation A)) ≤
      max (specNorm (∑ i, A i * (A i)ᴴ)) (specNorm (∑ i, (A i)ᴴ * A i)) := by
  rw [coefficientVariance_gramCoefficientDilation]
  refine (specNorm_fromBlocks_diagonal_le _ _).trans (max_le (le_max_left _ _) ?_)
  refine (specNorm_fromBlocks_diagonal_le _ _).trans (max_le (le_max_right _ _) ?_)
  simpa only [specNorm_zero] using
    le_max_of_le_right (specNorm_nonneg (∑ i, (A i)ᴴ * A i))

omit [Fintype ι] [DecidableEq ι] [DecidableEq d] in
/-- The true vectorized Gram is the original Gram plus its entrywise
conjugate. This retains the conjugation required for complex coefficients. -/
theorem coefficientVectorization_gram_gramCoefficientDilation
    (A : ι → Matrix d d ℂ) :
    (coefficientVectorization (gramCoefficientDilation A))ᴴ *
        coefficientVectorization (gramCoefficientDilation A) =
      (coefficientVectorization A)ᴴ * coefficientVectorization A +
        ((coefficientVectorization A)ᴴ * coefficientVectorization A).map star := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, coefficientVectorization,
    gramCoefficientDilation, gramCoefficientRow, dilation, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, Matrix.zero_apply, star_zero, mul_zero, Finset.sum_const_zero, zero_add,
    add_zero, star_star, Matrix.add_apply, Matrix.map_apply, star_sum, star_mul]
  apply congrArg₂ (· + ·)
  · rfl
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- Entry covariance of the actual positive Gram dilation has at most
twice the original squared covariance parameter, independently of dimension. -/
theorem specNorm_coefficientCovariance_gramCoefficientDilation_le
    (A : ι → Matrix d d ℂ) :
    specNorm (coefficientCovariance (gramCoefficientDilation A)) ≤
      2 * specNorm (coefficientCovariance A) := by
  have hH : specNorm (coefficientCovariance (gramCoefficientDilation A)) =
      specNorm ((coefficientVectorization (gramCoefficientDilation A))ᴴ *
        coefficientVectorization (gramCoefficientDilation A)) := by
    rw [coefficientCovariance, specNorm_mul_conjTranspose_self,
      ← specNorm_sq_eq_specNorm_conjTranspose_mul_self]
  have hA : specNorm ((coefficientVectorization A)ᴴ * coefficientVectorization A) =
      specNorm (coefficientCovariance A) := by
    rw [coefficientCovariance, specNorm_mul_conjTranspose_self,
      ← specNorm_sq_eq_specNorm_conjTranspose_mul_self]
  rw [hH, coefficientVectorization_gram_gramCoefficientDilation]
  calc
    _ ≤ specNorm ((coefficientVectorization A)ᴴ * coefficientVectorization A) +
        specNorm (((coefficientVectorization A)ᴴ * coefficientVectorization A).map star) :=
      specNorm_add_le _ _
    _ = _ := by rw [specNorm_map_star, hA]; ring


omit [DecidableEq ι] in
/-- The actual square-root variance of the Hermitian dilation is bounded
by the original non-Hermitian variance parameter. -/
theorem sqrt_specNorm_coefficientVariance_gramCoefficientDilation_le
    (A : ι → Matrix d d ℂ) :
    Real.sqrt (specNorm (coefficientVariance (gramCoefficientDilation A))) ≤
      Real.sqrt (max (specNorm (∑ i, A i * (A i)ᴴ))
        (specNorm (∑ i, (A i)ᴴ * A i))) :=
  Real.sqrt_le_sqrt (specNorm_coefficientVariance_gramCoefficientDilation_le A)

/-- The actual square-root entry covariance of the Hermitian dilation
has a universal factor two bound; this includes the zero family. -/
theorem sqrt_specNorm_coefficientCovariance_gramCoefficientDilation_le
    (A : ι → Matrix d d ℂ) :
    Real.sqrt (specNorm (coefficientCovariance (gramCoefficientDilation A))) ≤
      2 * Real.sqrt (specNorm (coefficientCovariance A)) := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (specNorm_nonneg _), mul_pow,
    Real.sq_sqrt (specNorm_nonneg _)]
  have h := specNorm_coefficientCovariance_gramCoefficientDilation_le A
  nlinarith [specNorm_nonneg (coefficientCovariance A)]

/-- The actual geometric variance/covariance scale of the Hermitian
linearization is at most twice the original quadratic source scale. -/
theorem sqrt_variance_covariance_gramCoefficientDilation_le
    (A : ι → Matrix d d ℂ) :
    Real.sqrt (Real.sqrt (specNorm (coefficientVariance (gramCoefficientDilation A))) *
      Real.sqrt (specNorm (coefficientCovariance (gramCoefficientDilation A)))) ≤
      2 * Real.sqrt
        (Real.sqrt (max (specNorm (∑ i, A i * (A i)ᴴ))
          (specNorm (∑ i, (A i)ᴴ * A i))) *
          Real.sqrt (specNorm (coefficientCovariance A))) := by
  have hV := sqrt_specNorm_coefficientVariance_gramCoefficientDilation_le A
  have hW := sqrt_specNorm_coefficientCovariance_gramCoefficientDilation_le A
  have hprod := mul_le_mul hV hW (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg
    (Real.sqrt_nonneg (max (specNorm (∑ i, A i * (A i)ᴴ))
      (specNorm (∑ i, (A i)ᴴ * A i))))
    (Real.sqrt_nonneg (specNorm (coefficientCovariance A)))]

end NLAlib
