import NLAlib.RandomMatrix.Gaussian.Comparison.ResolventOperatorInterpolation
import NLAlib.Probability.Moments.ExpectedResolventRemainder
import NLAlib.ForMathlib.Analysis.Calculus.InteriorDerivativeBound

/-! # Expected operator resolvents along full-covariance interpolation

Actual covariance cancellation and aggregate cubic remainders control the
operator norm of the endpoint difference. The estimate keeps the expected
aggregate square mass rather than summing scalar third moments.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ
local notation "C" => (ι × Fin 3) → E
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

open scoped Matrix.Norms.L2Operator in
/-- The actual matrix-valued interpolation is controlled by the expected
aggregate square mass of its transformed summands. The coefficient `72`
is universal and independent of both matrix size and summand count.
Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Section 6.4, Lemma 6.11.
atlas: matrix-resolvent-gaussian-universality (partial) -/
theorem specNorm_resamplingInterpolation_sub_le_square_mass
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) (hγ : HasGaussianLaw (id : E → E) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : E => z i), (fun z : E => z j); γ] =
        cov[(fun p : ι × C => resamplingTripleOriginal p i),
          (fun p : ι × C => resamplingTripleOriginal p j); resamplingTripleMeasure ν])
    (A : M) (hA : A.IsHermitian) {R : ℝ} (hR : 0 ≤ R)
    (hBound : ∀ i, ∀ᵐ x ∂ν i, specNorm (L x) ≤ R)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    specNorm (resamplingInterpolation ν γ (hermitianCoordinateResolvent A ζ) 1 -
      resamplingInterpolation ν γ (hermitianCoordinateResolvent A ζ) 0) ≤
      72 * (R * |ζ.im|⁻¹ ^ 4 + R ^ 3 * |ζ.im|⁻¹ ^ 6) *
        ∫ x : ι → E, specNorm (∑ i, (L (x i)) ^ 2) ∂Measure.pi ν := by
  have := hγ.isProbabilityMeasure
  let F : ℝ → M := resamplingInterpolation ν γ (hermitianCoordinateResolvent A ζ)
  let Y : ℝ := ∫ x : ι → E, specNorm (∑ i, (L (x i)) ^ 2) ∂Measure.pi ν
  let K : ℝ := 72 * (R * |ζ.im|⁻¹ ^ 4 + R ^ 3 * |ζ.im|⁻¹ ^ 6) * Y
  have hY : 0 ≤ Y := integral_nonneg fun _ => specNorm_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hFc : Continuous F := continuous_resamplingInterpolation ν hν γ _
    (continuous_hermitianCoordinateResolvent A hA ζ hζ) |ζ.im|⁻¹
    (specNorm_hermitianCoordinateResolvent_le A hA ζ hζ)
  have hInterior : ∀ t ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ F t ∧ specNorm (deriv F t) ≤ K := by
    intro t ht
    let a := Real.sqrt t
    let b := Real.sqrt (1 - t)
    let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
    let base : C × E → M := fun q => A + L
      (resamplingAffinePoint μ a b (∑ i, q.1 (i, 0)) q.2)
    let T : (ι × C) × E → M := fun q =>
      resolventCubicRemainder (base (q.1.2, q.2))
        (L (q.1.2 (q.1.1, 0) - q.1.2 (q.1.1, 1)))
        (L (q.1.2 (q.1.1, 0) - q.1.2 (q.1.1, 2))) a ζ
    let N : ℝ := Fintype.card ι
    let Q := (resamplingTripleMeasure ν).prod γ
    have hbase : Measurable base := by
      dsimp [base, resamplingAffinePoint]
      fun_prop
    have hbaseH : ∀ q, (base q).IsHermitian := fun q =>
      hA.add (isHermitian_hermitianMatrixFromRealCoordinates _)
    have he := integrable_and_specNorm_card_smul_integral_resolventCubicRemainder_le
      ν γ L base hbase.aemeasurable (ae_of_all _ hbaseH) hR
      (fun _ => ae_of_all _ fun _ => isHermitian_hermitianMatrixFromRealCoordinates _)
      hBound a ζ hζ
    have hEstimate : specNorm (N • ∫ q, T q ∂Q) ≤
        (96 * R * |ζ.im|⁻¹ ^ 4 + 288 * a ^ 2 * R ^ 3 * |ζ.im|⁻¹ ^ 6) * Y :=
      he.2.2
    have hd0 := integrable_and_hasDerivAt_resamplingInterpolation_resolventCubicRemainder
      ν hν γ hγ hmean hcov A hA ζ hζ ht.1 ht.2
    have hd : HasDerivAt F ((N * a / 4) • ∫ q, T q ∂Q) t := by
      have hdRaw := hd0.2
      dsimp only at hdRaw
      change HasDerivAt F ((N * a / 4) • ∫ q,
        resolventCubicRemainder
          (A + L (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2))
          (L (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1))
          (L (resamplingTripleOriginal q.1 - resamplingTripleSecond q.1)) a ζ ∂Q) t at hdRaw
      apply hdRaw.congr_deriv
      apply congrArg (fun v : M => (N * a / 4) • v)
      apply integral_congr_ae
      exact ae_of_all _ fun q => by
        dsimp only
        rw [resamplingTriple_difference, resamplingTriple_difference_second]
        rfl
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    have ha : 0 ≤ a := Real.sqrt_nonneg _
    have ha1 : a ≤ 1 := Real.sqrt_le_one.mpr ht.2.le
    have ha3 : a ^ 3 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ ha ha1 3
    have hscalar : N * a / 4 = (a / 4) * N := by ring
    rw [hscalar, mul_smul, specNorm_eq_norm, norm_smul,
      Real.norm_of_nonneg (div_nonneg ha (by norm_num))]
    calc
      _ ≤ (a / 4) *
          ((96 * R * |ζ.im|⁻¹ ^ 4 + 288 * a ^ 2 * R ^ 3 * |ζ.im|⁻¹ ^ 6) * Y) :=
        mul_le_mul_of_nonneg_left hEstimate (div_nonneg ha (by norm_num))
      _ ≤ K := by
        have hu : 0 ≤ R * |ζ.im|⁻¹ ^ 4 := by positivity
        have hv : 0 ≤ R ^ 3 * |ζ.im|⁻¹ ^ 6 := by positivity
        have hcoef : (a / 4) *
            (96 * R * |ζ.im|⁻¹ ^ 4 + 288 * a ^ 2 * R ^ 3 * |ζ.im|⁻¹ ^ 6) ≤
            72 * (R * |ζ.im|⁻¹ ^ 4 + R ^ 3 * |ζ.im|⁻¹ ^ 6) := by
          nlinarith [mul_nonneg (show 0 ≤ 72 - 24 * a by linarith) hu,
            mul_nonneg (show 0 ≤ 72 - 72 * a ^ 3 by linarith) hv]
        dsimp [K]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hY
  exact norm_sub_endpoints_le_of_hasDerivAt_Ioo hK hFc.continuousOn
    (fun t ht => (hInterior t ht).1.hasDerivAt) (fun t ht => (hInterior t ht).2)

end NLAlib
