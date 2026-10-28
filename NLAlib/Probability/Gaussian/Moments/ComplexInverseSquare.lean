import NLAlib.Probability.Gaussian.Basic.ComplexUnitary
import NLAlib.Probability.ChiSquare.ChiSquare

/-!
# Reciprocal squared norms of circular complex Gaussian vectors

Each circular complex coordinate has independent variance-one real and
imaginary parts. A `d`-coordinate squared norm therefore has `2d` real Gaussian
squares, and its reciprocal mean is `1/(2d-2)` for `d≥2`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- Realification expresses a complex squared norm as the sum of all real and
imaginary coordinate squares. -/
theorem sum_sq_realifyVector {n : Type*} [Fintype n] (z : n → ℂ) :
    (∑ i : n ⊕ n, realifyVector z i ^ 2) = ∑ i, Complex.normSq (z i) := by
  simp only [Fintype.sum_sum_type, realifyVector, Complex.normSq_apply,
    Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib]
  congr 1
  funext i
  ring

/-- The exact reciprocal squared norm is integrable for at least two complex
coordinates and has mean `1/(2d-2)` under the actual circular product law. -/
theorem integrable_and_integral_inv_sum_normSq_circularComplexGaussianVector
    {n : Type*} [Fintype n] (hn : 2 ≤ Fintype.card n) :
    Integrable (fun z : n → ℂ => (∑ i, Complex.normSq (z i))⁻¹)
      (circularComplexGaussianVector n) ∧
      ∫ z : n → ℂ, (∑ i, Complex.normSq (z i))⁻¹ ∂circularComplexGaussianVector n =
        1/(2*(Fintype.card n:ℝ)-2) := by
  have hd : 3 ≤ Fintype.card (n ⊕ n) := by simp only [Fintype.card_sum]; omega
  have hi := integrable_inv_sum_sq_gaussianVector (ι := n ⊕ n) hd
  have hv := integral_inv_sum_sq_gaussianVector (ι := n ⊕ n) hd
  have hZ := hasLaw_realifyVector_circularComplexGaussianVector (n := n)
  have hf : AEStronglyMeasurable (fun x : n ⊕ n → ℝ => (∑ i, x i^2)⁻¹)
      (gaussianVector (n ⊕ n)) := (by fun_prop : Measurable _).aestronglyMeasurable
  have hic : Integrable (fun z : n → ℂ => (∑ i, realifyVector z i^2)⁻¹)
      (circularComplexGaussianVector n) := by
    rw [← hZ.map_eq] at hi
    exact hi.comp_aemeasurable hZ.aemeasurable
  constructor
  · simpa only [sum_sq_realifyVector] using hic
  · have h := hZ.integral_comp hf
    simp only [Function.comp_apply, sum_sq_realifyVector] at h
    rw [h, hv]
    simp only [Fintype.card_sum, Nat.cast_add]
    congr 1
    ring

/-- The same exact inverse-norm moment holds after any complex coisometry,
with its native Gaussian product law and without assumed covariance data. -/
theorem integrable_and_integral_inv_sum_normSq_mulVec_circularComplexGaussianVector
    {n d : Type*} [Fintype n] [Fintype d] [DecidableEq d] [DecidableEq n]
    (U : Matrix d n ℂ) (hU : HasOrthonormalCols Uᴴ) (hd : 2 ≤ Fintype.card d) :
    Integrable (fun z : n → ℂ => (∑ i, Complex.normSq ((U*ᵥz) i))⁻¹)
      (circularComplexGaussianVector n) ∧
      ∫ z : n → ℂ, (∑ i, Complex.normSq ((U*ᵥz) i))⁻¹ ∂circularComplexGaussianVector n =
        1/(2*(Fintype.card d:ℝ)-2) := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_inv_sum_normSq_circularComplexGaussianVector hd
  have hZ := hasLaw_mulVec_circularComplexGaussianVector_orthonormalRows U hU
  have hf : AEStronglyMeasurable (fun z : d → ℂ => (∑ i, Complex.normSq (z i))⁻¹)
      (circularComplexGaussianVector d) := (by fun_prop : Measurable _).aestronglyMeasurable
  constructor
  · rw [← hZ.map_eq] at hi
    exact hi.comp_aemeasurable hZ.aemeasurable
  · exact (hZ.integral_comp hf).trans hv

end NLAlib
