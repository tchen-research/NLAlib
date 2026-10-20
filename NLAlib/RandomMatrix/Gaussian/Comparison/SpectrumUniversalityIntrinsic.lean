import NLAlib.RandomMatrix.Gaussian.Comparison.SpectrumUniversality
import NLAlib.Probability.Moments.BilinearWeakVarianceProbes

/-!
# Independent-sum spectral universality with the intrinsic variance parameters

This is the full native Hausdorff comparison: both variance parameters are
computed from the original marginal laws. The bilinear parameter agrees
with the supremum of the actual centered unit-sphere probe standard
deviations, and no moment or concentration budget is assumed.
Source: arXiv:2201.05142v3, Theorem 2.6.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι n Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [MeasurableSpace Ω]
local notation "M" => Matrix n n ℂ
local notation "J" => (n×n)⊕(n×n)

open scoped Matrix.Norms.L2Operator in
/-- The actual spectrum of a bounded independent centered Hermitian sum
is close to that of its mean- and full-covariance-matching Gaussian matrix,
at the exact intrinsic square-root, cubic and linear scale of the source.
The matrices may have any coupling, the deterministic mean is arbitrary,
and zero radius and singular Gaussian covariance are included. The native
bilinear parameter is exactly the source unit-sphere standard-deviation
supremum, by `sqrt_bilinearWeakVariance_eq_sSup_unitSphere`.
Source: arXiv:2201.05142v3, Theorem 2.6, with universal constant 80000000.
atlas: independent-sum-spectrum-universality -/
theorem measureReal_hausdorffDist_spectra_gt_le_of_matching_gaussian
    (ν : ι → Measure M) [∀ i,IsProbabilityMeasure (ν i)]
    (hHerm : ∀ i,∀ᵐ A ∂ν i,A.IsHermitian)
    {R : ℝ} (hR : 0≤R) (hBound : ∀ i,∀ᵐ A ∂ν i,specNorm A≤R)
    (hmeanν : ∀ i,∫ A : M,A ∂ν i=0)
    (ρ : Measure M) [IsGaussian ρ] (hρHerm : ∀ᵐ A ∂ρ,A.IsHermitian)
    (A₀ : M) (hA₀ : A₀.IsHermitian) (hmean : (∫ A : M,A ∂ρ)=A₀)
    (hcov : ∀ a b : J,
      cov[(fun A : M => matrixRealCoordinates A a),
        (fun A : M => matrixRealCoordinates A b);ρ] =
      cov[(fun x : ι → M => matrixRealCoordinates (∑ i,x i) a),
        (fun x : ι → M => matrixRealCoordinates (∑ i,x i) b);Measure.pi ν])
    (hd : 2≤Fintype.card n) {t : ℝ} (ht : 0≤t)
    (μ : Measure Ω) (S : Ω → ι → M) (G : Ω → M)
    (hS : HasLaw S (Measure.pi ν) μ) (hG : HasLaw G ρ μ) :
    let σ := Real.sqrt (specNorm (∑ i,∫ A : M,A^2 ∂ν i))
    let s := Real.sqrt (bilinearWeakVariance
      ((Measure.pi ν).map (fun x : ι → M => A₀+∑ i,x i)))
    μ.real {ω | 80000000*(s*Real.sqrt t+R^(1/3 : ℝ)*σ^(2/3 : ℝ)*t^(2/3 : ℝ)+R*t) <
      Metric.hausdorffDist (spectrum ℝ (A₀+∑ i,S ω i)) (spectrum ℝ (G ω))} ≤
        (Fintype.card n : ℝ)*Real.exp (-t) := by
  let σ := Real.sqrt (specNorm (∑ i,∫ A : M,A^2 ∂ν i))
  let s := Real.sqrt (bilinearWeakVariance
    ((Measure.pi ν).map (fun x : ι → M => A₀+∑ i,x i)))
  have hσ : 0≤σ := Real.sqrt_nonneg _
  have hs : 0≤s := Real.sqrt_nonneg _
  have hvariance : specNorm (∑ i,∫ A : M,A^2 ∂ν i)≤σ^2 :=
    (Real.sq_sqrt (specNorm_nonneg _)).symm.le
  have hbilinear (a b : EuclideanSpace ℂ n) (ha : ‖a‖≤1) (hb : ‖b‖≤1) :
      (∑ i,∫ A : M,‖star a.ofLp ⬝ᵥ (A *ᵥ b.ofLp)‖^2 ∂ν i)≤s^2 := by
    have hh := sum_integral_norm_sq_bilinear_le_bilinearWeakVariance_shifted_sum
      ν (fun _ (A : M) => A) (fun _ => measurable_id) hBound hmeanν A₀ a b ha hb
    simpa only [s,Real.sq_sqrt (bilinearWeakVariance_nonneg _)] using hh
  have hsumMean : (∫ x : ι → M,∑ i,x i ∂Measure.pi ν)=0 := by
    have hZi (i : ι) : Integrable (id : M → M) (ν i) :=
      Integrable.of_bound measurable_id.aestronglyMeasurable R (hBound i)
    rw [integral_finsetSum Finset.univ (f := fun i (x : ι → M) => x i) (fun i _ =>
      (measurePreserving_eval ν i).integrable_comp_of_integrable (hZi i))]
    simp only [integral_eval,hmeanν,Finset.sum_const_zero]
  have hmean' : (∫ A : M,A ∂ρ)=A₀+∫ x : ι → M,∑ i,x i ∂Measure.pi ν := by
    simpa only [hsumMean,add_zero] using hmean
  have hh := measureReal_hausdorffDist_spectra_gt_spectralScale_le ν hHerm hR hs hσ
    hBound hmeanν hvariance hbilinear ρ hρHerm A₀ hA₀ hmean' hcov hd ht μ S G hS hG
  rw [independentSumSpectralScale_eq hR hσ ht] at hh
  exact hh

end NLAlib
