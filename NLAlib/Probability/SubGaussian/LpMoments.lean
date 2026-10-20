import NLAlib.Probability.SubGaussian.Moments
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Integer Lp bounds for sub-Gaussian fluctuations

The actual even scalar moments give an explicit square-root growth bound,
including a zero variance proxy. Centering at the expectation then compares
the Lp norm of an observable with its realized value outside a Gaussian tail.
These estimates supply the scalar moment step in arXiv:2201.05142v3,
Lemma 7.3.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A sub-Gaussian fluctuation has the scale-normalized strict Gaussian
tail, including a zero variance proxy. -/
theorem measureReal_sqrt_mul_lt_abs_le_of_hasSubgaussianMGF
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | Real.sqrt c * t < |X ω|} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hz := h.ae_eq_zero_of_hasSubgaussianMGF_zero
    have he : {ω | Real.sqrt (0 : ℝ≥0) * t < |X ω|} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hz] with ω hω
      apply propext
      change (Real.sqrt (0 : ℝ≥0) * t < |X ω|) ↔ False
      simp only [Pi.zero_apply] at hω
      simp [hω]
    rw [measureReal_congr he, measureReal_empty]
    positivity
  · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hb := measureReal_lt_abs_le_of_hasSubgaussianMGF h
      (mul_nonneg (Real.sqrt_nonneg (c : ℝ)) ht)
    have he : -(Real.sqrt c * t) ^ 2 / (2 * c) = -t ^ 2 / 2 := by
      have hsqrt : Real.sqrt (c : ℝ) ^ 2 = (c : ℝ) := Real.sq_sqrt c.2
      have hmul := congrArg (fun r : ℝ => r * t ^ 2) hsqrt
      rw [mul_pow]
      field_simp [hc']
      nlinarith
    rwa [he] at hb

/-- An actual sub-Gaussian fluctuation has even Lp norm at most
`sqrt (4*c*p)`. Integrability follows from its MGF, including when `c=0`. -/
theorem lpNorm_two_mul_le_sqrt_of_hasSubgaussianMGF
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    {p : ℕ} (hp : 0 < p) :
    lpNorm X (2 * (p : ℝ≥0∞)) μ ≤ Real.sqrt (4 * (c : ℝ) * p) := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have h2p : (0 : ℝ) < (2 * p : ℕ) := by positivity
  have hGamma : (p : ℝ) * Real.Gamma p = (p.factorial : ℝ) := by
    rw [← Real.Gamma_add_one hpr.ne', Real.Gamma_nat_eq_factorial]
  have hmoment := integral_abs_rpow_le_of_hasSubgaussianMGF h h2p
  have he : (((2 * p : ℕ) : ℝ) / 2) = (p : ℝ) := by push_cast; ring
  rw [he] at hmoment
  have hfac : (p.factorial : ℝ) ≤ (p : ℝ) ^ p := by
    exact_mod_cast Nat.factorial_le_pow p
  have htwo : (2 : ℝ) ≤ 2 ^ p := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by omega : 1 ≤ p)
  have hmoment' : (∫ ω, |X ω| ^ ((2 * p : ℕ) : ℝ) ∂μ) ≤
      (4 * (c : ℝ) * p) ^ p := by
    calc
      _ ≤ 2 * (2 * (c : ℝ)) ^ p * (p.factorial : ℝ) := by
        calc
          _ ≤ ((2 * p : ℕ) : ℝ) * (2 * (c : ℝ)) ^ (p : ℝ) * Real.Gamma p :=
            hmoment
          _ = 2 * (2 * (c : ℝ)) ^ p * ((p : ℝ) * Real.Gamma p) := by
            simp only [Nat.cast_mul, Nat.cast_ofNat, Real.rpow_natCast]
            ring
          _ = _ := by rw [hGamma]
      _ ≤ 2 * (2 * (c : ℝ)) ^ p * (p : ℝ) ^ p := by gcongr
      _ ≤ 2 ^ p * (2 * (c : ℝ)) ^ p * (p : ℝ) ^ p := by gcongr
      _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; ring
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by finiteness)
    h.aemeasurable.aestronglyMeasurable]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast,
    Real.norm_eq_abs]
  calc
    _ ≤ ((4 * (c : ℝ) * p) ^ p) ^ (2 * (p : ℝ))⁻¹ := by
      apply Real.rpow_le_rpow
      · exact integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
      · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmoment'
      · positivity
    _ = Real.sqrt (4 * (c : ℝ) * p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
      congr 1
      field_simp

/-- Centered sub-Gaussian control gives an actual Lp bound around the mean.
No integrability premise on the uncentered observable is needed. -/
theorem lpNorm_le_integral_add_sqrt_of_centered_hasSubgaussianMGF
    {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun ω => X ω - ∫ y, X y ∂μ) c μ)
    {p : ℕ} (hp : 0 < p) :
    lpNorm X (2 * (p : ℝ≥0∞)) μ ≤
      (∫ ω, X ω ∂μ) + Real.sqrt (4 * (c : ℝ) * p) := by
  have hmean : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg hX
  have he : X = (fun _ : Ω => ∫ y, X y ∂μ) +
      (fun ω => X ω - ∫ y, X y ∂μ) := by ext ω; simp
  calc
    _ ≤ lpNorm (fun _ : Ω => ∫ y, X y ∂μ) (2 * (p : ℝ≥0∞)) μ +
        lpNorm (fun ω => X ω - ∫ y, X y ∂μ) (2 * (p : ℝ≥0∞)) μ := by
      conv_lhs => rw [he]
      apply lpNorm_add_le (memLp_const _)
      exact_mod_cast (by omega : 1 ≤ 2 * p)
    _ = (∫ y, X y ∂μ) +
        lpNorm (fun ω => X ω - ∫ y, X y ∂μ) (2 * (p : ℝ≥0∞)) μ := by
      rw [lpNorm_const' (by positivity) (by finiteness), probReal_univ, Real.one_rpow,
        mul_one, Real.norm_eq_abs, abs_of_nonneg hmean]
    _ ≤ _ := add_le_add le_rfl (lpNorm_two_mul_le_sqrt_of_hasSubgaussianMGF h hp)

/-- A realized nonnegative observable exceeds its actual even Lp norm,
up to the square-root moment loss and a sub-Gaussian fluctuation.
The strict event also covers zero fluctuation parameters. -/
theorem measureReal_lt_lpNorm_sub_le_of_centered_hasSubgaussianMGF
    {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun ω => X ω - ∫ y, X y ∂μ) c μ)
    {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | X ω + Real.sqrt (4 * (c : ℝ) * p) + t <
      lpNorm X (2 * (p : ℝ≥0∞)) μ} ≤
      2 * Real.exp (-t ^ 2 / (2 * c)) := by
  have hm := lpNorm_le_integral_add_sqrt_of_centered_hasSubgaussianMGF hX h hp
  apply (measureReal_mono (μ := μ) (fun ω hω => ?_)).trans
    (measureReal_lt_abs_le_of_hasSubgaussianMGF h ht)
  change t < |X ω - ∫ y, X y ∂μ|
  have hs := neg_le_abs (X ω - ∫ y, X y ∂μ)
  change X ω + Real.sqrt (4 * (c : ℝ) * p) + t <
    lpNorm X (2 * (p : ℝ≥0∞)) μ at hω
  linarith

end NLAlib
