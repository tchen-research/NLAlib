import NLAlib.Probability.Gaussian.Basic.ComplexUnitary
import NLAlib.Probability.Gaussian.Basic.StandardVector
import Mathlib.MeasureTheory.Integral.Prod

/-!
# First and second moments of complex Gaussian linear forms

Realification identifies the two real parts of a complex linear form with
ordinary real Gaussian linear forms. This gives exact native moments without
assuming a covariance matrix or invoking a complex Gaussian integration API.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- The squared modulus of an actual circular complex Gaussian linear form
has expectation twice the squared coefficient norm and is integrable. -/
theorem integrable_and_integral_normSq_dotProduct_circularComplexGaussianVector
    {n : Type*} [Fintype n] (c : n → ℂ) :
    Integrable (fun z : n → ℂ => Complex.normSq (c ⬝ᵥ z)) (circularComplexGaussianVector n) ∧
      ∫ z, Complex.normSq (c ⬝ᵥ z) ∂circularComplexGaussianVector n =
        2*∑ i, Complex.normSq (c i) := by
  let u : n ⊕ n → ℝ := Sum.elim (fun i => (c i).re) (fun i => -(c i).im)
  let v : n ⊕ n → ℝ := Sum.elim (fun i => (c i).im) (fun i => (c i).re)
  have he (z : n → ℂ) : Complex.normSq (c ⬝ᵥ z)=
      (u ⬝ᵥ realifyVector z)^2+(v ⬝ᵥ realifyVector z)^2 := by
    simp [Complex.normSq_apply,dotProduct,Fintype.sum_sum_type,u,v,realifyVector,
      Complex.mul_re,Complex.mul_im,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      Finset.sum_neg_distrib,neg_mul]
    ring
  have hZ := hasLaw_realifyVector_circularComplexGaussianVector (n := n)
  have hsu : AEStronglyMeasurable (fun x : n ⊕ n → ℝ => (u ⬝ᵥ x)^2)
      (gaussianVector (n ⊕ n)) := (by fun_prop : Measurable _).aestronglyMeasurable
  have hsv : AEStronglyMeasurable (fun x : n ⊕ n → ℝ => (v ⬝ᵥ x)^2)
      (gaussianVector (n ⊕ n)) := (by fun_prop : Measurable _).aestronglyMeasurable
  have hiu : Integrable (fun z : n → ℂ => (u ⬝ᵥ realifyVector z)^2)
      (circularComplexGaussianVector n) := by
    have h := integrable_dotProduct_sq_gaussianVector u
    rw [← hZ.map_eq] at h
    exact h.comp_aemeasurable hZ.aemeasurable
  have hiv : Integrable (fun z : n → ℂ => (v ⬝ᵥ realifyVector z)^2)
      (circularComplexGaussianVector n) := by
    have h := integrable_dotProduct_sq_gaussianVector v
    rw [← hZ.map_eq] at h
    exact h.comp_aemeasurable hZ.aemeasurable
  have hpu := (hZ.integral_comp hsu).trans (integral_dotProduct_sq_gaussianVector u)
  have hpv := (hZ.integral_comp hsv).trans (integral_dotProduct_sq_gaussianVector v)
  simp only [Function.comp_apply] at hpu hpv
  simp_rw [he]
  refine ⟨hiu.add hiv,?_⟩
  rw [integral_add hiu hiv,hpu,hpv]
  simp only [EuclideanSpace.real_norm_sq_eq,Fintype.sum_sum_type,u,v,Sum.elim_inl,
    Sum.elim_inr,neg_sq,Complex.normSq_apply,Finset.sum_add_distrib]
  ring

/-- Actual circular complex Gaussian linear forms are integrable and have
zero complex mean. The proof preserves the full joint product law. -/
theorem integrable_and_integral_dotProduct_circularComplexGaussianVector
    {n : Type*} [Fintype n] (c : n → ℂ) :
    Integrable (fun z : n → ℂ => c ⬝ᵥ z) (circularComplexGaussianVector n) ∧
      ∫ z, c ⬝ᵥ z ∂circularComplexGaussianVector n=0 := by
  classical
  obtain ⟨hi,hv⟩ := integrable_and_integral_normSq_dotProduct_circularComplexGaussianVector c
  have hm : Measurable (fun z : n → ℂ => c ⬝ᵥ z) := by fun_prop
  have hfi : Integrable (fun z : n → ℂ => c ⬝ᵥ z) (circularComplexGaussianVector n) :=
    ((integrable_const 1).add hi).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        change ‖c ⬝ᵥ z‖ ≤ 1+Complex.normSq (c ⬝ᵥ z)
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [sq_nonneg (‖c ⬝ᵥ z‖-1),norm_nonneg (c ⬝ᵥ z)])
  have hU : HasOrthonormalCols (-1 : Matrix n n ℂ) := by
    change (-1 : Matrix n n ℂ)ᴴ*(-1)=1
    rw [Matrix.conjTranspose_neg,Matrix.conjTranspose_one,neg_mul_neg,Matrix.one_mul]
  have hn := hasLaw_mulVec_circularComplexGaussianVector_unitary (-1 : Matrix n n ℂ) hU
  have he : (fun z : n → ℂ => (-1 : Matrix n n ℂ)*ᵥz)=fun z => -z := by
    funext z
    rw [Matrix.neg_mulVec,Matrix.one_mulVec]
  rw [he] at hn
  have h := hn.integral_comp hm.aestronglyMeasurable
  simp only [Function.comp_apply,dotProduct_neg,integral_neg] at h
  refine ⟨hfi,?_⟩
  apply Complex.ext
  · have hh := congrArg Complex.re h
    simp only [Complex.neg_re] at hh
    change (∫ z, c ⬝ᵥ z ∂circularComplexGaussianVector n).re=0
    linarith
  · have hh := congrArg Complex.im h
    simp only [Complex.neg_im] at hh
    change (∫ z, c ⬝ᵥ z ∂circularComplexGaussianVector n).im=0
    linarith

end NLAlib
