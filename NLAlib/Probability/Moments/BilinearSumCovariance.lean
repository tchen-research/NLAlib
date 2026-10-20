import NLAlib.Probability.Moments.BilinearCovariance
import NLAlib.Probability.Concentration.Matrix.BilinearVariance

/-!
# Actual bilinear variance budgets of covariance-matched sums

The native independent centered sum and any square-integrable law with its
full real/imaginary entry covariance have exactly the same centered bilinear
second moments. This derives the Gaussian sigma-star budget used in
arXiv:2201.05142v3 from the original increment laws.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {ι n Ω : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)

open scoped Matrix.Norms.L2Operator in
/-- Full entry covariance matching transports the exact complex bilinear
variance of the actual centered independent sum to the proxy law. The mean
of the proxy may differ, and its Gaussianity is unnecessary. -/
theorem integral_norm_sq_centered_bilinear_eq_sum_of_covariance_eq
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (Z : ι → Ω → M) (hZm : ∀ i, Measurable (Z i))
    {R : ℝ} (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i = 0)
    (ρ : Measure M) [IsProbabilityMeasure ρ] (hρ : MemLp (id : M → M) 2 ρ)
    (hcov : ∀ i j : J,
      cov[(fun A : M => matrixRealCoordinates A i),
        (fun A : M => matrixRealCoordinates A j); ρ] =
      cov[(fun x : ι → Ω => matrixRealCoordinates (∑ k, Z k (x k)) i),
        (fun x : ι → Ω => matrixRealCoordinates (∑ k, Z k (x k)) j); Measure.pi ν])
    (v w : n → ℂ) :
    (∫ A : M, ‖star v ⬝ᵥ ((A - ∫ B, B ∂ρ) *ᵥ w)‖ ^ 2 ∂ρ) =
      ∑ i, ∫ ω, ‖star v ⬝ᵥ (Z i ω *ᵥ w)‖ ^ 2 ∂ν i := by
  have hZi (i : ι) : MemLp (Z i) 2 (ν i) :=
    MemLp.of_bound (hZm i).aestronglyMeasurable R (hZ i)
  have hsum : MemLp (fun x : ι → Ω => ∑ i, Z i (x i)) 2 (Measure.pi ν) := by
    exact memLp_finsetSum Finset.univ fun i _ =>
      (hZi i).comp_measurePreserving (measurePreserving_eval ν i)
  have hm : (∫ x : ι → Ω, ∑ i, Z i (x i) ∂Measure.pi ν) = 0 := by
    rw [integral_finsetSum Finset.univ (f := fun i (x : ι → Ω) => Z i (x i)) (fun i _ =>
      (measurePreserving_eval ν i).integrable_comp_of_integrable ((hZi i).integrable one_le_two))]
    simp only [integral_comp_eval (μ := ν) (i := _) (hZi _).aestronglyMeasurable,
      hmean, Finset.sum_const_zero]
  have h := integral_norm_sq_centered_bilinear_eq_of_matrix_covariance_eq
    hsum hρ (fun i j => (hcov i j).symm) v w
  simp only [hm, sub_zero, id_eq] at h
  rw [← h]
  simpa only [WithLp.ofLp_toLp] using
    integral_norm_sq_bilinear_sum_pi_eq_sum ν Z hZm hZ hmean
      (WithLp.toLp 2 v) (WithLp.toLp 2 w)

end NLAlib
