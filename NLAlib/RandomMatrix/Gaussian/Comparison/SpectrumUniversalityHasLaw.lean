import NLAlib.RandomMatrix.Gaussian.Comparison.SpectrumUniversalityIntrinsic
import Mathlib.Probability.HasLaw

/-!
# Spectral universality for actual independent random matrices

Independence supplies the full joint product law. All original means,
full entry covariances, marginal square expectations and the intrinsic
bilinear variance are transported to the native spectral comparison.
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
/-- Independent bounded centered Hermitian random matrices and any jointly
Gaussian Hermitian matrix with their actual mean and full covariance have
close native real spectra in probability. Both variance parameters are
computed from the original random matrices, the deterministic mean may be
arbitrary, and the Gaussian matrix may have any coupling with the sum.
The constant is universal; no spectral, moment or concentration certificate
is supplied. The source sigma-star equals the literal unit-sphere probe
standard-deviation supremum by the checked weak-variance identification.
Source: arXiv:2201.05142v3, Theorem 2.6.
atlas: independent-sum-spectrum-universality -/
theorem measureReal_hausdorffDist_spectra_sum_gaussian_gt_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ι → Ω → M) (hZm : ∀ i,Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hHerm : ∀ i,∀ᵐ ω ∂μ,(Z i ω).IsHermitian)
    {R : ℝ} (hR : 0≤R) (hBound : ∀ i,∀ᵐ ω ∂μ,specNorm (Z i ω)≤R)
    (hmeanZ : ∀ i,∫ ω,Z i ω ∂μ=0)
    (G : Ω → M) (hGaussian : HasGaussianLaw G μ)
    (hGHerm : ∀ᵐ ω ∂μ,(G ω).IsHermitian)
    (A₀ : M) (hA₀ : A₀.IsHermitian) (hmean : (∫ ω,G ω ∂μ)=A₀)
    (hcov : ∀ a b : J,
      cov[(fun ω => matrixRealCoordinates (G ω) a),
        (fun ω => matrixRealCoordinates (G ω) b);μ] =
      cov[(fun ω => matrixRealCoordinates (A₀+∑ i,Z i ω) a),
        (fun ω => matrixRealCoordinates (A₀+∑ i,Z i ω) b);μ])
    (hd : 2≤Fintype.card n) {t : ℝ} (ht : 0≤t) :
    let σ := Real.sqrt (specNorm (∑ i,∫ ω,Z i ω^2 ∂μ))
    let s := Real.sqrt (bilinearWeakVariance (μ.map (fun ω => A₀+∑ i,Z i ω)))
    μ.real {ω | 80000000*(s*Real.sqrt t+R^(1/3 : ℝ)*σ^(2/3 : ℝ)*t^(2/3 : ℝ)+R*t) <
      Metric.hausdorffDist (spectrum ℝ (A₀+∑ i,Z i ω)) (spectrum ℝ (G ω))} ≤
        (Fintype.card n : ℝ)*Real.exp (-t) := by
  let ν (i : ι) := μ.map (Z i)
  let hZ (i : ι) : HasLaw (Z i) (ν i) μ := ⟨(hZm i).aemeasurable,rfl⟩
  let (i : ι) : IsProbabilityMeasure (ν i) := (hZ i).isProbabilityMeasure_iff.mp inferInstance
  have hPi : HasLaw (fun ω i => Z i ω) (Measure.pi ν) μ := hIndep.hasLaw_pi hZ
  let ρ := μ.map G
  let : IsGaussian ρ := hGaussian.isGaussian_map
  have hG : HasLaw G ρ μ := ⟨hGaussian.aemeasurable,rfl⟩
  have hHset : MeasurableSet {A : M | A.IsHermitian} := by
    change MeasurableSet {A : M | Aᴴ=A}
    exact (isClosed_eq (by fun_prop : Continuous (fun A : M => Aᴴ)) continuous_id).measurableSet
  have hνHerm (i : ι) : ∀ᵐ A ∂ν i,A.IsHermitian := by
    rw [← (hZ i).map_eq]
    exact (ae_map_iff (hZ i).aemeasurable hHset).mpr (hHerm i)
  have hνBound (i : ι) : ∀ᵐ A ∂ν i,specNorm A≤R := by
    rw [← (hZ i).map_eq]
    exact (ae_map_iff (hZ i).aemeasurable (by
      change MeasurableSet {A : M | ‖A‖≤R}
      exact measurableSet_le measurable_id.norm measurable_const)).mpr (hBound i)
  have hνMean (i : ι) : (∫ A : M,A ∂ν i)=0 := by
    rw [← (hZ i).integral_eq,hmeanZ]
  have hρHerm : ∀ᵐ A ∂ρ,A.IsHermitian := by
    rw [← hG.map_eq]
    exact (ae_map_iff hG.aemeasurable hHset).mpr hGHerm
  have hρMean : (∫ A : M,A ∂ρ)=A₀ := by rw [← hG.integral_eq,hmean]
  have hνInt (i : ι) : Integrable (id : M → M) (ν i) :=
    Integrable.of_bound aestronglyMeasurable_id R (hνBound i)
  have hSumInt : Integrable (fun x : ι → M => ∑ i,x i) (Measure.pi ν) :=
    integrable_finsetSum _ (fun i _ => integrable_eval (μ:=ν) (i:=i) (hνInt i))
  have hShiftM : Measurable (fun x : ι → M => A₀+∑ i,x i) := by fun_prop
  have hCoordsInt : Integrable (fun x : ι → M => matrixRealCoordinates (∑ i,x i))
      (Measure.pi ν) :=
    matrixRealCoordinatesContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hSumInt
  have hScalarInt (a : J) : Integrable
      (fun x : ι → M => matrixRealCoordinates (∑ i,x i) a) (Measure.pi ν) :=
    (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : J => ℝ) a).integrable_comp hCoordsInt
  have hCovProd (a b : J) :
      cov[(fun A : M => matrixRealCoordinates A a),
        (fun A : M => matrixRealCoordinates A b);ρ] =
      cov[(fun x : ι → M => matrixRealCoordinates (∑ i,x i) a),
        (fun x : ι → M => matrixRealCoordinates (∑ i,x i) b);Measure.pi ν] := by
    have hca : Measurable (fun A : M => matrixRealCoordinates A a) :=
      (measurable_pi_apply a).comp measurable_matrixRealCoordinates
    have hcb : Measurable (fun A : M => matrixRealCoordinates A b) :=
      (measurable_pi_apply b).comp measurable_matrixRealCoordinates
    calc
      _ = cov[(fun ω => matrixRealCoordinates (G ω) a),
          (fun ω => matrixRealCoordinates (G ω) b);μ] :=
        (hG.covariance_fun_comp hca.aemeasurable hcb.aemeasurable).symm
      _ = cov[(fun ω => matrixRealCoordinates (A₀+∑ i,Z i ω) a),
          (fun ω => matrixRealCoordinates (A₀+∑ i,Z i ω) b);μ] := hcov a b
      _ = cov[(fun x : ι → M => matrixRealCoordinates (A₀+∑ i,x i) a),
          (fun x : ι → M => matrixRealCoordinates (A₀+∑ i,x i) b);Measure.pi ν] :=
        hPi.covariance_fun_comp (hca.comp hShiftM).aemeasurable (hcb.comp hShiftM).aemeasurable
      _ = _ := by
        simp only [map_add,Pi.add_apply]
        rw [covariance_const_add_left (hScalarInt a),covariance_const_add_right (hScalarInt b)]
  have hSqMeas : Measurable (fun A : M => A^2) := by
    simpa only [pow_two,id_eq] using
      (measurable_id.matrix_mul measurable_id : Measurable (fun A : M => A*A))
  have hνSq (i : ι) : Integrable (fun A : M => A^2) (ν i) := by
    refine Integrable.of_bound hSqMeas.aestronglyMeasurable (R^2) ?_
    filter_upwards [hνBound i] with A hA
    exact (norm_pow_le' A (by norm_num : (0 : ℕ)<2)).trans
      (pow_le_pow_left₀ (norm_nonneg A) hA 2)
  have hSq : (∑ i,∫ ω,Z i ω^2 ∂μ)=∑ i,∫ A : M,A^2 ∂ν i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (hZ i).integral_comp (hνSq i).aestronglyMeasurable
  have hShiftLaw : HasLaw (fun ω => A₀+∑ i,Z i ω)
      ((Measure.pi ν).map (fun x : ι → M => A₀+∑ i,x i)) μ :=
    (show HasLaw (fun x : ι → M => A₀+∑ i,x i)
      ((Measure.pi ν).map (fun x : ι → M => A₀+∑ i,x i)) (Measure.pi ν) from
        ⟨hShiftM.aemeasurable,rfl⟩).fun_comp hPi
  have hh := measureReal_hausdorffDist_spectra_gt_le_of_matching_gaussian
    ν hνHerm hR hνBound hνMean ρ hρHerm A₀ hA₀ hρMean hCovProd hd ht μ
      (fun ω i => Z i ω) G hPi hG
  rw [← hSq,← hShiftLaw.map_eq] at hh
  exact hh

end NLAlib
