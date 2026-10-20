import NLAlib.Probability.Transforms.ResolventMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Actual resolvent operator-norm moments

The expected normalized Gram moment and the actual scalar Lp norm of the
spectral norm differ by at most the exact dimension factor. These are the
native expectation bridges used with Markov's inequality in
Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 7.3.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Matrix ENNReal
namespace NLAlib

variable {n Ω : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace Ω]

open scoped Matrix.Norms.L2Operator in
/-- The scalar norm of a nonreal Hermitian resolvent lies in every finite
Lp space, without any moment assumption on the random matrix. -/
theorem memLp_specNorm_resolvent
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Matrix n n ℂ)
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) (q : ℝ≥0∞) :
    MemLp (fun ω => specNorm (resolvent (X ω) ζ)) q μ := by
  apply MemLp.of_bound
    (((measurable_matrix_resolvent ζ).comp_aemeasurable hXm).norm.aestronglyMeasurable)
    (|ζ.im|⁻¹)
  filter_upwards [hX] with ω hω
  change ‖specNorm (resolvent (X ω) ζ)‖ ≤ |ζ.im|⁻¹
  rw [Real.norm_of_nonneg (specNorm_nonneg _)]
  exact hω.specNorm_resolvent_le hζ

open scoped Matrix.Norms.L2Operator in
private theorem integrable_specNorm_resolvent_pow
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Matrix n n ℂ)
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) (q : ℕ) :
    Integrable (fun ω => specNorm (resolvent (X ω) ζ) ^ q) μ := by
  apply Integrable.of_bound
    ((((measurable_matrix_resolvent ζ).comp_aemeasurable hXm).norm).pow_const q).aestronglyMeasurable
    (|ζ.im|⁻¹ ^ q)
  filter_upwards [hX] with ω hω
  change ‖specNorm (resolvent (X ω) ζ) ^ q‖ ≤ |ζ.im|⁻¹ ^ q
  rw [Real.norm_of_nonneg (pow_nonneg (specNorm_nonneg _) _)]
  exact pow_le_pow_left₀ (specNorm_nonneg _) (hω.specNorm_resolvent_le hζ) q

open scoped Matrix.Norms.L2Operator in
/-- The actual rooted expected normalized Gram moment is at most the
actual scalar even Lp norm of the spectral norm. Empty shapes are included. -/
theorem integral_resolventEvenMoment_rpow_inv_le_lpNorm_specNorm
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Matrix n n ℂ)
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    (∫ ω, resolventEvenMoment (X ω) ζ p ∂μ) ^ (1 / ((2 * p : ℕ) : ℝ)) ≤
      lpNorm (fun ω => specNorm (resolvent (X ω) ζ)) (2 * (p : ℝ≥0∞)) μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by finiteness)
    (memLp_specNorm_resolvent μ X hXm hX hζ (2 * (p : ℝ≥0∞))).1]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast,
    Real.norm_of_nonneg (specNorm_nonneg _),
    show (2 * (p : ℝ)) = ((2*p : ℕ) : ℝ) by simp, Real.rpow_natCast]
  have hi := (integrable_and_integral_resolventEvenMoment_le μ X hXm hX hζ hp).1
  have hn := integrable_specNorm_resolvent_pow μ X hXm hX hζ (2*p)
  have hb := integral_mono hi hn (fun ω => resolventEvenMoment_le_specNorm_pow (X ω) ζ hp)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.rpow_natCast, one_div] using
    Real.rpow_le_rpow
      (integral_nonneg fun ω => resolventEvenMoment_nonneg (X ω) ζ hp) hb
      (by positivity : 0 ≤ (2 * (p : ℝ))⁻¹)

open scoped Matrix.Norms.L2Operator in
/-- Conversely, the actual even scalar Lp norm is at most the actual
rooted expected normalized Gram moment times `d^(1/(2p))`.
No matrix moment or integrability hypotheses are supplied. -/
theorem lpNorm_specNorm_resolvent_le_card_rpow_mul_integral_resolventEvenMoment_rpow_inv
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Matrix n n ℂ)
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    lpNorm (fun ω => specNorm (resolvent (X ω) ζ)) (2 * (p : ℝ≥0∞)) μ ≤
      (Fintype.card n : ℝ) ^ (1 / ((2 * p : ℕ) : ℝ)) *
        (∫ ω, resolventEvenMoment (X ω) ζ p ∂μ) ^ (1 / ((2 * p : ℕ) : ℝ)) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by finiteness)
    (memLp_specNorm_resolvent μ X hXm hX hζ (2 * (p : ℝ≥0∞))).1]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast,
    Real.norm_of_nonneg (specNorm_nonneg _),
    show (2 * (p : ℝ)) = ((2*p : ℕ) : ℝ) by simp, Real.rpow_natCast]
  have hi := (integrable_and_integral_resolventEvenMoment_le μ X hXm hX hζ hp).1
  have hn := integrable_specNorm_resolvent_pow μ X hXm hX hζ (2*p)
  have hb := integral_mono hn (hi.const_mul (Fintype.card n : ℝ))
    (fun ω => specNorm_resolvent_pow_le_card_mul_resolventEvenMoment (X ω) ζ hp)
  rw [integral_const_mul] at hb
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ ≤ ((Fintype.card n : ℝ) * ∫ ω, resolventEvenMoment (X ω) ζ p ∂μ) ^
        (2 * (p : ℝ))⁻¹ := by
      apply Real.rpow_le_rpow
      · exact integral_nonneg fun ω => pow_nonneg (specNorm_nonneg _) _
      · exact hb
      · positivity
    _ = _ := by rw [Real.mul_rpow (by positivity)
          (integral_nonneg fun ω => resolventEvenMoment_nonneg (X ω) ζ hp)]
                simp only [one_div]

end NLAlib
