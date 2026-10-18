import NLAlib.ForMathlib.Analysis.InnerProductSpace.CoerciveInverse
import NLAlib.ForMathlib.Analysis.Matrix.QuadraticPositiveMap

/-! # Matrix inverse bounds from imaginary-part coercivity

Loewner coercivity of the native imaginary part controls negative right
inverses in the actual Euclidean operator norm, including nonnormal matrices.
Source: Ajanki--Erdős--Krüger, Proposition 2.1, equation (4.1).
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule

namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Euclidean inner product evaluates the native matrix quadratic probe. -/
theorem inner_toEuclideanCLM_eq_matrixQuadraticFormCLM
    (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    inner ℂ x (toEuclideanCLM (n := n) (𝕜 := ℂ) A x) = matrixQuadraticFormCLM x.ofLp A := by
  simp only [PiLp.inner_apply, matrixQuadraticFormCLM_apply, dotProduct,
    RCLike.inner_apply', starRingEnd_apply, Pi.star_apply]
  rfl

/-- Loewner imaginary coercivity gives the corresponding quadratic energy bound. -/
theorem mul_norm_sq_le_im_inner_of_imaginaryPart_ge
    {A : Matrix n n ℂ} {η : ℝ}
    (hA : η • (1 : Matrix n n ℂ) ≤ (imaginaryPart A : Matrix n n ℂ))
    (x : EuclideanSpace ℂ n) :
    η * ‖x‖ ^ 2 ≤ (inner ℂ x (toEuclideanCLM (n := n) (𝕜 := ℂ) A x)).im := by
  have h := RCLike.re_le_re ((matrixQuadraticPositiveMap x.ofLp).monotone hA)
  rw [inner_toEuclideanCLM_eq_matrixQuadraticFormCLM, im_matrixQuadraticFormCLM]
  have hnorm : (matrixQuadraticFormCLM x.ofLp 1).re = ‖x‖ ^ 2 := by
    rw [← inner_toEuclideanCLM_eq_matrixQuadraticFormCLM]
    simp [← Complex.ofReal_pow]
  change matrixRealQuadraticFormCLM x.ofLp (η • (1 : Matrix n n ℂ)) ≤
    matrixRealQuadraticFormCLM x.ofLp (imaginaryPart A : Matrix n n ℂ) at h
  rw [map_smul, smul_eq_mul] at h
  change η * (matrixQuadraticFormCLM x.ofLp 1).re ≤ _ at h
  rwa [hnorm] at h

/-- A coercive imaginary part bounds any negative right inverse by `1/η`. -/
theorem norm_le_inv_of_mul_eq_neg_one_of_imaginaryPart_ge
    {T M : Matrix n n ℂ} {η : ℝ} (hη : 0 < η)
    (hTM : T * M = -1)
    (hT : η • (1 : Matrix n n ℂ) ≤ (imaginaryPart T : Matrix n n ℂ)) :
    ‖M‖ ≤ η⁻¹ := by
  rw [cstar_norm_def]
  apply ContinuousLinearMap.norm_le_inv_of_im_inner_coercive
    (toEuclideanCLM (n := n) (𝕜 := ℂ) T)
    (toEuclideanCLM (n := n) (𝕜 := ℂ) M) hη
  · intro x
    have h := congrArg (fun A : Matrix n n ℂ => toEuclideanCLM (n := n) (𝕜 := ℂ) A x) hTM
    simpa using h
  · exact mul_norm_sq_le_im_inner_of_imaginaryPart_ge hT

/-- A negative right inverse transports imaginary parts by congruence. -/
theorem imaginaryPart_eq_conjTranspose_mul_of_mul_eq_neg_one
    {T M : Matrix n n ℂ} (hTM : T * M = -1) :
    (imaginaryPart M : Matrix n n ℂ) =
      Mᴴ * (imaginaryPart T : Matrix n n ℂ) * M := by
  have hs : Mᴴ * Tᴴ = -1 := by
    simpa only [conjTranspose_mul, conjTranspose_neg, conjTranspose_one] using
      congrArg Matrix.conjTranspose hTM
  have hdiff : Mᴴ * (T - Tᴴ) * M = M - Mᴴ := by
    rw [mul_sub, sub_mul, mul_assoc, hTM, hs]
    simp [sub_eq_add_neg, add_comm]
  simp only [imaginaryPart_apply_coe, Matrix.star_eq_conjTranspose]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hdiff]

end Matrix
