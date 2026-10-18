import NLAlib.RandomMatrix.Gaussian.Comparison.MatrixResolventUniversality
import NLAlib.Matrix.Functions.ResolventMeasurability
import Mathlib.Probability.HasLaw

/-! # Resolvent universality for actual independent random matrices

Actual marginal laws and independence produce the full product law. Both
means and every real and imaginary covariance are transported from the
actual random matrices, together with their native resolvent expectations
and raw squared-increment expectations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ

open scoped Matrix.Norms.L2Operator in
/-- Independent bounded Hermitian random matrices and an actual Hermitian
Gaussian matrix with the same actual mean and full real and imaginary
covariance have expected resolvents within the explicit universal bound.
The random matrices may live on unrelated probability spaces. Every law,
moment and integral transport is derived from the displayed hypotheses;
the second-moment matrix is expressed using the actual original space.
For noncentered increments it is the raw second-moment matrix; centered
increments give the usual variance proxy. Empty increment families,
matrix dimension one and singular Gaussian covariance are allowed.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Theorem 2.10 and
Section 6.4, with explicit constant 288 and `log (2d)`.
atlas: matrix-resolvent-gaussian-universality -/
theorem specNorm_integral_resolvent_sum_sub_gaussian_le_of_hasLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'}
    (Z : ι → Ω → M) (ν : ι → Measure M)
    (hZ : ∀ i, HasLaw (Z i) (ν i) P) (hIndep : iIndepFun Z P)
    (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R) (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R)
    (G : Ω' → M) (ρ : Measure M) (hG : HasLaw G ρ Q)
    (hGaussian : HasGaussianLaw (fun ω => matrixRealCoordinates (G ω)) Q)
    (hGHerm : ∀ᵐ ω ∂Q, (G ω).IsHermitian)
    (A₀ : M) (hA₀ : A₀.IsHermitian)
    (hmean : (∫ ω, G ω ∂Q) = ∫ ω, A₀ + ∑ i, Z i ω ∂P)
    (hcov : ∀ a b : J,
      cov[(fun ω => matrixRealCoordinates (G ω) a),
        (fun ω => matrixRealCoordinates (G ω) b); Q] =
      cov[(fun ω => matrixRealCoordinates (A₀ + ∑ i, Z i ω) a),
        (fun ω => matrixRealCoordinates (A₀ + ∑ i, Z i ω) b); P])
    (ζ : ℂ) (hζ : 0 < ζ.im) :
    specNorm ((∫ ω, resolvent (A₀ + ∑ i, Z i ω) ζ ∂P) -
      ∫ ω, resolvent (G ω) ζ ∂Q) ≤
      288 * (R * specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂P) +
        R ^ 3 * Real.log (2 * Fintype.card n)) / ζ.im ^ 4 := by
  let (i : ι) : IsProbabilityMeasure (ν i) := (hZ i).isProbabilityMeasure_iff.mp inferInstance
  let := hGaussian.isProbabilityMeasure
  have hPi : HasLaw (fun ω i => Z i ω) (Measure.pi ν) P := hIndep.hasLaw_pi hZ
  have hCoordLaw : HasLaw (fun ω => matrixRealCoordinates (G ω))
      (ρ.map matrixRealCoordinates) Q :=
    (show HasLaw (matrixRealCoordinates : M → E) (ρ.map matrixRealCoordinates) ρ from
      ⟨measurable_matrixRealCoordinates.aemeasurable, rfl⟩).fun_comp hG
  have hρ : HasGaussianLaw (matrixRealCoordinates : M → E) ρ := by
    constructor
    rw [← hCoordLaw.map_eq]
    exact hGaussian.isGaussian_map
  let := hρ.isProbabilityMeasure
  have hHset : MeasurableSet {A : M | A.IsHermitian} := by
    change MeasurableSet {A : M | Aᴴ = A}
    exact (isClosed_eq (by fun_prop : Continuous (fun A : M => Aᴴ)) continuous_id).measurableSet
  have hρHerm : ∀ᵐ A ∂ρ, A.IsHermitian := by
    rw [← hG.map_eq]
    exact (ae_map_iff hG.aemeasurable hHset).mpr hGHerm
  have hνInt (i : ι) : Integrable (id : M → M) (ν i) :=
    Integrable.of_bound aestronglyMeasurable_id R (hBound i)
  have hSumInt : Integrable (fun x : ι → M => ∑ i, x i) (Measure.pi ν) :=
    integrable_finsetSum _ (fun i _ => integrable_eval (μ := ν) (i := i) (hνInt i))
  have hShiftM : Measurable (fun x : ι → M => A₀ + ∑ i, x i) := by fun_prop
  have hShiftMean : (∫ ω, A₀ + ∑ i, Z i ω ∂P) =
      ∫ x : ι → M, A₀ + ∑ i, x i ∂Measure.pi ν :=
    hPi.integral_comp hShiftM.aestronglyMeasurable
  have hMeanProd : (∫ A : M, A ∂ρ) = A₀ + ∫ x : ι → M, ∑ i, x i ∂Measure.pi ν := by
    rw [← hG.integral_eq, hmean, hShiftMean,
      integral_add (integrable_const A₀) hSumInt]
    simp only [integral_const, probReal_univ, one_smul]
  have hCoordsInt : Integrable (fun x : ι → M => matrixRealCoordinates (∑ i, x i))
      (Measure.pi ν) :=
    matrixRealCoordinatesContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hSumInt
  have hScalarInt (a : J) : Integrable
      (fun x : ι → M => matrixRealCoordinates (∑ i, x i) a) (Measure.pi ν) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) a).integrable_comp hCoordsInt
  have hCovProd (a b : J) :
      cov[(fun A : M => matrixRealCoordinates A a),
        (fun A : M => matrixRealCoordinates A b); ρ] =
      cov[(fun x : ι → M => matrixRealCoordinates (∑ i, x i) a),
        (fun x : ι → M => matrixRealCoordinates (∑ i, x i) b); Measure.pi ν] := by
    have hca : Measurable (fun A : M => matrixRealCoordinates A a) :=
      (measurable_pi_apply a).comp measurable_matrixRealCoordinates
    have hcb : Measurable (fun A : M => matrixRealCoordinates A b) :=
      (measurable_pi_apply b).comp measurable_matrixRealCoordinates
    calc
      _ = cov[(fun ω => matrixRealCoordinates (G ω) a),
          (fun ω => matrixRealCoordinates (G ω) b); Q] :=
        (hG.covariance_fun_comp hca.aemeasurable hcb.aemeasurable).symm
      _ = cov[(fun ω => matrixRealCoordinates (A₀ + ∑ i, Z i ω) a),
          (fun ω => matrixRealCoordinates (A₀ + ∑ i, Z i ω) b); P] := hcov a b
      _ = cov[(fun x : ι → M => matrixRealCoordinates (A₀ + ∑ i, x i) a),
          (fun x : ι → M => matrixRealCoordinates (A₀ + ∑ i, x i) b); Measure.pi ν] :=
        hPi.covariance_fun_comp (hca.comp hShiftM).aemeasurable (hcb.comp hShiftM).aemeasurable
      _ = _ := by
        simp only [map_add, Pi.add_apply]
        rw [covariance_const_add_left (hScalarInt a), covariance_const_add_right (hScalarInt b)]
  have hSqMeas : Measurable (fun A : M => A ^ 2) := by
    simpa only [pow_two, id_eq] using
      (measurable_id.matrix_mul measurable_id : Measurable (fun A : M => A * A))
  have hνSq (i : ι) : Integrable (fun A : M => A ^ 2) (ν i) := by
    refine Integrable.of_bound hSqMeas.aestronglyMeasurable (R ^ 2) ?_
    filter_upwards [hBound i] with A hA
    rw [pow_two]
    exact (norm_mul_le _ _).trans (by
      simpa only [pow_two] using (sq_le_sq₀ (norm_nonneg A) hR).mpr hA)
  have hSq : (∑ i, ∫ ω, Z i ω ^ 2 ∂P) = ∑ i, ∫ A : M, A ^ 2 ∂ν i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (hZ i).integral_comp (hνSq i).aestronglyMeasurable
  have hleft : (∫ ω, resolvent (A₀ + ∑ i, Z i ω) ζ ∂P) =
      ∫ x : ι → M, resolvent (A₀ + ∑ i, x i) ζ ∂Measure.pi ν :=
    hPi.integral_comp ((measurable_matrix_resolvent ζ).comp hShiftM).aestronglyMeasurable
  have hright : (∫ ω, resolvent (G ω) ζ ∂Q) = ∫ A : M, resolvent A ζ ∂ρ :=
    hG.integral_comp (measurable_matrix_resolvent ζ).aestronglyMeasurable
  let : MeasurableSpace ι := ⊤
  have h := specNorm_integral_resolvent_sum_sub_gaussian_le ν hHerm hR hBound
    ρ hρ hρHerm A₀ hA₀ hMeanProd hCovProd ζ hζ
  rw [← hleft, ← hright, ← hSq] at h
  exact h

end NLAlib
