import NLAlib.Probability.Gaussian.Moments.SeriesPartialTranspose

/-! # Covariance-sensitive Hermitian Gaussian series norms

The finite Hermite estimate and the actual coefficient-block variance and
entry-covariance comparisons give the leading constant two with an explicit
universal correction constant. No free comparison model or asymptotic
freeness theorem is used. Empty coefficient families are included.
Source: Bandeira--Boedihardjo--van Handel (2023), Corollary 2.2;
finite Hermite reroute of 2026-10-16.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

/-- The coefficient-block correction scale is bounded by the geometric mean
of the usual variance scale and the unnormalized entry-covariance scale. -/
theorem coefficientBlockKappa_le_sqrt_variance_covariance [Nonempty ι] [Nonempty d]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlockKappa A ≤
      Real.sqrt (Real.sqrt (specNorm (coefficientVariance A)) *
        Real.sqrt (specNorm (coefficientCovariance A))) := by
  have hh := (coefficientBlock_variance_covariance_bounds A hA).2.2.2
  have hκ : 0 ≤ coefficientBlockKappa A := Real.sqrt_nonneg _
  apply (Real.le_sqrt hκ (by positivity)).mpr
  simpa only [pow_two] using mul_le_mul (hh.trans (min_le_left _ _))
    (hh.trans (min_le_right _ _)) hκ (Real.sqrt_nonneg _)

private theorem sqrt_log_le_correction (D : ℕ) (hD : 2 ≤ D) :
    Real.sqrt (Real.log (D : ℝ)) ≤
      ((Real.log 2) ^ (1 / 4 : ℝ))⁻¹ * (Real.log (D : ℝ)) ^ (3 / 4 : ℝ) := by
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlog : Real.log 2 ≤ Real.log (D : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hD)
  have hDlog : 0 < Real.log (D : ℝ) := htwo.trans_le hlog
  have hquarter : (Real.log 2) ^ (1 / 4 : ℝ) ≤ (Real.log (D : ℝ)) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow htwo.le hlog (by norm_num)
  have hden : 0 < (Real.log 2) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos htwo _
  have hh := mul_le_mul_of_nonneg_right hquarter (Real.sqrt_nonneg (Real.log (D : ℝ)))
  rw [Real.sqrt_eq_rpow] at hh
  rw [← Real.rpow_add hDlog, show (1 / 4 : ℝ) + 1 / 2 = 3 / 4 by norm_num] at hh
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hden).mpr
  simpa only [Real.sqrt_eq_rpow, mul_comm] using hh

/-- The covariance-sensitive Gaussian expected norm bound with explicit
universal correction constant `6/(log 2)^(1/4)`. The coefficient covariance
uses unnormalized Frobenius vectorization. Empty coefficient families and
zero variance are included.
Source: Bandeira--Boedihardjo--van Handel (2023), Corollary 2.2;
finite Hermite reroute of 2026-10-16.
atlas: gaussian-series-covariance-sensitive-norm (partial) -/
theorem integral_specNorm_gaussianSeries_le_covarianceSensitive
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (hd : 2 ≤ Fintype.card d) :
    (∫ x, specNorm (∑ i, x i • A i) ∂gaussianVector ι) ≤
      2 * Real.sqrt (specNorm (coefficientVariance A)) +
        (6 / (Real.log 2) ^ (1 / 4 : ℝ)) *
          Real.sqrt (Real.sqrt (specNorm (coefficientVariance A)) *
            Real.sqrt (specNorm (coefficientCovariance A))) *
              (Real.log (Fintype.card d)) ^ (3 / 4 : ℝ) := by
  haveI : Nonempty d := Fintype.card_pos_iff.mp (show 0 < Fintype.card d by omega)
  cases isEmpty_or_nonempty ι with
  | inl hι => simp [coefficientVariance, specNorm_zero]
  | inr hι =>
    have hκ := coefficientBlockKappa_le_sqrt_variance_covariance A hA
    have hlog := sqrt_log_le_correction (Fintype.card d) hd
    apply (integral_specNorm_gaussianSeries_le_partialTranspose A hA).trans
    apply add_le_add le_rfl
    have hh := mul_le_mul hκ hlog (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hh' := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 6 by norm_num)
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh'

open scoped Matrix.Norms.L2Operator in
/-- The covariance-sensitive bound applies on any probability space through
the joint standard Gaussian law, with the same universal explicit constant.
Source: Bandeira--Boedihardjo--van Handel (2023), Corollary 2.2.
atlas: gaussian-series-covariance-sensitive-norm (partial) -/
theorem integral_specNorm_gaussianSeries_le_covarianceSensitive_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (hd : 2 ≤ Fintype.card d)
    {ξ : Ω → ι → ℝ} (hξ : HasLaw ξ (gaussianVector ι) μ) :
    (∫ ω, specNorm (∑ i, ξ ω i • A i) ∂μ) ≤
      2 * Real.sqrt (specNorm (coefficientVariance A)) +
        (6 / (Real.log 2) ^ (1 / 4 : ℝ)) *
          Real.sqrt (Real.sqrt (specNorm (coefficientVariance A)) *
            Real.sqrt (specNorm (coefficientCovariance A))) *
              (Real.log (Fintype.card d)) ^ (3 / 4 : ℝ) := by
  have hf : Continuous (fun x : ι → ℝ => specNorm (∑ i, x i • A i)) := by
    simp only [specNorm_eq_norm]
    fun_prop
  rw [show (∫ ω, specNorm (∑ i, ξ ω i • A i) ∂μ) =
      ∫ x, specNorm (∑ i, x i • A i) ∂gaussianVector ι from
    hξ.integral_comp hf.aestronglyMeasurable]
  exact integral_specNorm_gaussianSeries_le_covarianceSensitive A hA hd

/-- The explicit correction constant in the covariance-sensitive theorem
is a strictly positive universal real number.
atlas: gaussian-series-covariance-sensitive-norm (partial) -/
theorem covarianceSensitiveCorrectionConstant_pos :
    0 < (6 / (Real.log 2) ^ (1 / 4 : ℝ)) := by
  apply div_pos (by norm_num)
  exact Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _

end NLAlib
