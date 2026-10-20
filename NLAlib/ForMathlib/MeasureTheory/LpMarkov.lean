import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Markov tails at a multiple of the actual Lp norm

The strict form includes zero Lp norm. The exponential multiple is convenient
for high-moment spectral arguments.
-/

noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace MeasureTheory

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → E}

/-- Markov's inequality at an actual integer Lp norm, with the zero-norm
case included by the strict event. -/
theorem measureReal_lt_mul_lpNorm_le_inv_pow {q : ℕ} (hq : 0 < q)
    (hX : MemLp X (q : ℝ≥0∞) μ) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a * lpNorm X (q : ℝ≥0∞) μ < ‖X ω‖} ≤ (a ^ q)⁻¹ := by
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by positivity
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hzero : lpNorm X (q : ℝ≥0∞) μ = 0
  · have hz := (lpNorm_eq_zero hX hq0).mp hzero
    have he : {ω | a * lpNorm X (q : ℝ≥0∞) μ < ‖X ω‖} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hz] with ω hω
      simp only [Pi.zero_apply] at hω
      apply propext
      change (a * lpNorm X (q : ℝ≥0∞) μ < ‖X ω‖) ↔ False
      simp [hzero, hω]
    rw [measureReal_congr he, measureReal_empty]
    positivity
  have hL : 0 < lpNorm X (q : ℝ≥0∞) μ :=
    lt_of_le_of_ne lpNorm_nonneg (Ne.symm hzero)
  have hi : Integrable (fun ω => ‖X ω‖ ^ (q : ℝ)) μ := by
    exact (integrable_norm_rpow_iff hX.1 hq0 (by simp)).mpr hX
  have hi' : Integrable (fun ω => ‖X ω‖ ^ q) μ := by
    simpa only [Real.rpow_natCast] using hi
  have hm : (∫ ω, ‖X ω‖ ^ q ∂μ) = lpNorm X (q : ℝ≥0∞) μ ^ q := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hq0 (by simp) hX.1]
    simp only [ENNReal.toReal_natCast]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun _ =>
      Real.rpow_nonneg (norm_nonneg _) _), inv_mul_cancel₀ hqr.ne', Real.rpow_one]
    simp only [Real.rpow_natCast]
  have hs : {ω | a * lpNorm X (q : ℝ≥0∞) μ < ‖X ω‖} ⊆
      {ω | (a * lpNorm X (q : ℝ≥0∞) μ) ^ q ≤ ‖X ω‖ ^ q} := by
    intro ω hω
    exact pow_le_pow_left₀ (mul_pos ha hL).le hω.le q
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => pow_nonneg (norm_nonneg (X ω)) q)
    hi' ((a * lpNorm X (q : ℝ≥0∞) μ) ^ q)
  have ht : 0 < (a * lpNorm X (q : ℝ≥0∞) μ) ^ q := pow_pos (mul_pos ha hL) q
  calc
    _ ≤ μ.real {ω | (a * lpNorm X (q : ℝ≥0∞) μ) ^ q ≤ ‖X ω‖ ^ q} :=
      measureReal_mono hs
    _ ≤ (∫ ω, ‖X ω‖ ^ q ∂μ) / (a * lpNorm X (q : ℝ≥0∞) μ) ^ q :=
      (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hmarkov)
    _ = (a ^ q)⁻¹ := by rw [hm, mul_pow]; field_simp

/-- The norm of an actual Lq random variable exceeds `exp(1)` times its
Lq norm with probability at most `exp(-q)`, including zero norm. -/
theorem measureReal_lt_exp_mul_lpNorm_le_exp_neg {q : ℕ} (hq : 0 < q)
    (hX : MemLp X (q : ℝ≥0∞) μ) :
    μ.real {ω | Real.exp 1 * lpNorm X (q : ℝ≥0∞) μ < ‖X ω‖} ≤ Real.exp (-(q : ℝ)) := by
  have h := measureReal_lt_mul_lpNorm_le_inv_pow hq hX (Real.exp_pos 1)
  convert h using 1
  rw [← Real.exp_nat_mul, ← Real.exp_neg]
  simp

end MeasureTheory
