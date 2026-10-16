import NLAlib.Matrix.Structured.RectangularDilationBounds
import NLAlib.Probability.Gaussian.Moments.SeriesPartialTranspose
import NLAlib.Probability.SubGaussian.GaussianSeries

/-!
# Ordinary and covariance-sensitive subgaussian rectangular matrix series

The actual Gaussian partial-transpose theorem, exact rectangular-dilation
parameters, and the scalar Gaussian convex comparison supply both linear
estimates needed by finite matrix-chaos recursion. Constants are explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]
  [DecidableEq ι] [DecidableEq m] [DecidableEq n]
  [Nonempty ι] [Nonempty m] [Nonempty n]

private theorem sum_smul_realCoefficientDilation (B : ι → Matrix m n ℝ) (g : ι → ℝ) :
    (∑ i, g i • realCoefficientDilation B i) =
      dilation ((∑ i, g i • B i).map Complex.ofReal) := by
  ext (a | a) (b | b) <;>
    simp [realCoefficientDilation, dilation, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_mul]

private theorem specNorm_sum_smul_realCoefficientDilation
    (B : ι → Matrix m n ℝ) (g : ι → ℝ) :
    specNorm (∑ i, g i • realCoefficientDilation B i) = specNorm (∑ i, g i • B i) := by
  rw [sum_smul_realCoefficientDilation, specNorm_dilation]
  simpa only [Complex.coe_algebraMap] using
    specNorm_map_ofReal (𝕜 := ℂ) (∑ i, g i • B i)

/-- Ordinary and covariance-sensitive Gaussian linear estimates share a budget
`t ≥ 1` with `log(2(rows+cols)) ≤ t²`. The second estimate confines the
logarithmic factor to the actual entry-covariance block norm. -/
theorem integral_specNorm_gaussian_rectangular_blocks_le
    (B : ι → Matrix m n ℝ) {t : ℝ} (ht : 1 ≤ t)
    (hlog : Real.log (2 * ((Fintype.card m : ℝ) + Fintype.card n)) ≤ t ^ 2) :
    ((∫ g, specNorm (∑ i, g i • B i) ∂gaussianVector ι) ≤
      10 * t * (specNorm (coefficientRow B) + specNorm (coefficientColumn B))) ∧
    ((∫ g, specNorm (∑ i, g i • B i) ∂gaussianVector ι) ≤
      10 * (specNorm (coefficientRow B) + specNorm (coefficientColumn B) +
        t * specNorm (coefficientEntryRows B))) := by
  let D := realCoefficientDilation B
  let σ := Real.sqrt (specNorm (coefficientVariance D))
  let κ := coefficientBlockKappa D
  let R := specNorm (coefficientRow B) + specNorm (coefficientColumn B)
  let V := specNorm (coefficientEntryRows B)
  let L := Real.sqrt (Real.log (Fintype.card (m ⊕ n)))
  have hR0 : 0 ≤ R := add_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  have hV0 : 0 ≤ V := specNorm_nonneg _
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hσ : σ ≤ R := sqrt_specNorm_variance_realCoefficientDilation_le B
  have hb := (coefficientBlock_variance_covariance_bounds D
    (isHermitian_realCoefficientDilation B)).2.2.2
  have hκσ : κ ≤ σ := hb.trans (min_le_left _ _)
  have hκV : κ ≤ Real.sqrt 2 * V := by
    exact (hb.trans (min_le_right _ _)).trans_eq
      (sqrt_specNorm_covariance_realCoefficientDilation B)
  have hL : L ≤ t := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨ht0, ?_⟩
    have hd : 0 < (Fintype.card m : ℝ) + Fintype.card n := by positivity
    have hsmall := Real.log_le_log hd (show
      (Fintype.card m : ℝ) + Fintype.card n ≤
        2 * ((Fintype.card m : ℝ) + Fintype.card n) by linarith)
    simpa only [Fintype.card_sum, Nat.cast_add] using hsmall.trans hlog
  have hG : (∫ g, specNorm (∑ i, g i • B i) ∂gaussianVector ι) ≤
      2 * σ + 6 * κ * L := by
    have h := integral_specNorm_gaussianSeries_le_partialTranspose D
      (isHermitian_realCoefficientDilation B)
    simpa only [D, specNorm_sum_smul_realCoefficientDilation] using h
  constructor
  · have hk : κ * L ≤ R * t :=
      mul_le_mul (hκσ.trans hσ) hL (Real.sqrt_nonneg _) hR0
    have htr : 0 ≤ (t - 1) * R := mul_nonneg (sub_nonneg.mpr ht) hR0
    change (∫ g, specNorm (∑ i, g i • B i) ∂gaussianVector ι) ≤ 10 * t * R
    nlinarith only [hG, hσ, hk, htr, hR0]
  · have hk : κ * L ≤ (Real.sqrt 2 * V) * t :=
      mul_le_mul hκV hL (Real.sqrt_nonneg _) (by positivity)
    have hs : 6 * Real.sqrt 2 ≤ 10 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    have hc : 0 ≤ (10 - 6 * Real.sqrt 2) * (V * t) :=
      mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg hV0 ht0)
    change (∫ g, specNorm (∑ i, g i • B i) ∂gaussianVector ι) ≤ 10 * (R + t * V)
    nlinarith only [hG, hσ, hk, hc, hR0]

variable (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

open scoped Matrix.Norms.L2Operator in
/-- A centered real subgaussian rectangular series has an ordinary block-norm
bound with constant `100 K t`; the exponential-square input also proves all
needed scalar integrability. -/
theorem integral_specNorm_subgaussian_rectangular_le
    (K : ℝ) (hK : 0 < K) (hcenter : ∀ i, ∫ x, x ∂ν i = 0)
    (hpsi : ∀ i, ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν i ≤ 2)
    (B : ι → Matrix m n ℝ) {t : ℝ} (ht : 1 ≤ t)
    (hlog : Real.log (2 * ((Fintype.card m : ℝ) + Fintype.card n)) ≤ t ^ 2) :
    (∫ y, specNorm (∑ i, y i • B i) ∂Measure.pi ν) ≤
      (100 * K * t) * (specNorm (coefficientRow B) + specNorm (coefficientColumn B)) := by
  have hc := integral_norm_sum_smul_pi_le_gaussian_of_lintegral_exp_sq ν K hK hcenter hpsi B
  have hg := (integral_specNorm_gaussian_rectangular_blocks_le B ht hlog).1
  simp only [← specNorm_eq_norm] at hc
  apply hc.trans
  have h := mul_le_mul_of_nonneg_left hg (show 0 ≤ 10 * K by positivity)
  convert h using 1 <;> ring

open scoped Matrix.Norms.L2Operator in
/-- A centered real subgaussian rectangular series has a dimension-free leading
variance term and a logarithmic loss only on its actual entry-covariance block.
The constant `100 K` follows from Gaussian partial transpose and scalar convex
comparison; no free-spectrum comparison is assumed. -/
theorem integral_specNorm_subgaussian_rectangular_strong_le
    (K : ℝ) (hK : 0 < K) (hcenter : ∀ i, ∫ x, x ∂ν i = 0)
    (hpsi : ∀ i, ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν i ≤ 2)
    (B : ι → Matrix m n ℝ) {t : ℝ} (ht : 1 ≤ t)
    (hlog : Real.log (2 * ((Fintype.card m : ℝ) + Fintype.card n)) ≤ t ^ 2) :
    (∫ y, specNorm (∑ i, y i • B i) ∂Measure.pi ν) ≤
      (100 * K) * (specNorm (coefficientRow B) + specNorm (coefficientColumn B)) +
        (100 * K * t) * specNorm (coefficientEntryRows B) := by
  have hc := integral_norm_sum_smul_pi_le_gaussian_of_lintegral_exp_sq ν K hK hcenter hpsi B
  have hg := (integral_specNorm_gaussian_rectangular_blocks_le B ht hlog).2
  simp only [← specNorm_eq_norm] at hc
  apply hc.trans
  have h := mul_le_mul_of_nonneg_left hg (show 0 ≤ 10 * K by positivity)
  convert h using 1 <;> ring

end NLAlib
