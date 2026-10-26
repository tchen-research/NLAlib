import NLAlib.Probability.Gaussian.Moments.NaturalMoments
import NLAlib.ForMathlib.MeasureTheory.MomentInterpolation
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Lower bounds on real Gaussian moments

The rooted absolute `p`th moment of a scalar standard Gaussian is at least
`sqrt(p)/4` for every real `p ≥ 2`. The proof compares with the even moment
at `2 floor(p/2)`, bounds its odd-factor product below by a factorial, and
uses the explicit Stirling lower bound. Integrability is part of the API.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- Every nonnegative real absolute power of a scalar standard Gaussian is
integrable. This follows from the actual Gaussian `MemLp` theorem. -/
theorem integrable_abs_rpow_gaussianReal (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun z : ℝ => |z| ^ p) (gaussianReal 0 1) := by
  have hh := (memLp_id_gaussianReal' (μ := 0) (v := 1)
    (ENNReal.ofReal p) ENNReal.ofReal_ne_top).integrable_norm_rpow'
  simpa only [ENNReal.toReal_ofReal hp, Real.norm_eq_abs, id_eq] using hh

private theorem pow_div_four_le_gaussianEvenMoment (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) / 4) ^ m ≤ gaussianEvenMoment m := by
  have hmR : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hπ := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hm0
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi * m) := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi * m by positivity)
    have hn := Real.sqrt_nonneg (2 * Real.pi * m)
    nlinarith
  have hexp : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_three]
  have hbase : (m : ℝ) / 4 ≤ m / Real.exp 1 := by
    apply (div_le_div_iff₀ (by norm_num) (Real.exp_pos 1)).mpr
    exact mul_le_mul_of_nonneg_left hexp hm0
  calc
    ((m : ℝ) / 4) ^ m ≤ ((m : ℝ) / Real.exp 1) ^ m := pow_le_pow_left₀ (by positivity) hbase m
    _ ≤ Real.sqrt (2 * Real.pi * m) * ((m : ℝ) / Real.exp 1) ^ m :=
      le_mul_of_one_le_left (by positivity) hroot
    _ ≤ m.factorial := Stirling.le_factorial_stirling m
    _ ≤ gaussianEvenMoment m := factorial_le_gaussianEvenMoment m

private theorem sqrt_div_four_le_even_moment_root (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt ((m : ℝ) / 4) ≤ gaussianEvenMoment m ^ (2 * (m : ℝ))⁻¹ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hroot := Real.rpow_le_rpow (show (0 : ℝ) ≤ ((m : ℝ) / 4) ^ m by positivity)
    (pow_div_four_le_gaussianEvenMoment m hm)
    (show 0 ≤ (2 * (m : ℝ))⁻¹ by positivity)
  have heq : (((m : ℝ) / 4) ^ m) ^ (2 * (m : ℝ))⁻¹ = Real.sqrt ((m : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show (0 : ℝ) ≤ (m : ℝ) / 4 by positivity),
      Real.sqrt_eq_rpow]
    congr 1
    field_simp
  rwa [heq] at hroot

/-- For every real exponent at least two, the standard Gaussian rooted
absolute moment is at least `sqrt(p)/4`. The proof uses its actual even
moments, Stirling's explicit lower bound, and monotonicity of rooted moments
on a probability space. -/
theorem sqrt_div_four_le_integral_abs_rpow_root_gaussianReal
    {p : ℝ} (hp : 2 ≤ p) :
    Real.sqrt p / 4 ≤ (∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1) ^ p⁻¹ := by
  have hp0 : 0 < p := by linarith
  let m := ⌊p / 2⌋₊
  have hm : 1 ≤ m := Nat.floor_pos.mpr (by linarith)
  have hmR : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hmp : 2 * (m : ℝ) ≤ p := by
    have hh := Nat.floor_le (show 0 ≤ p / 2 by positivity)
    change (m : ℝ) ≤ p / 2 at hh
    linarith
  have hpm : p / 4 ≤ (m : ℝ) := by
    have hh := Nat.lt_floor_add_one (p / 2)
    change p / 2 < (m : ℝ) + 1 at hh
    linarith
  have hscalar :
      (∫ z : ℝ, |z| ^ (2 * (m : ℝ)) ∂gaussianReal 0 1) = gaussianEvenMoment m := by
    have he : 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
    rw [he]
    simp only [Real.rpow_natCast, even_two_mul, Even.pow_abs]
    exact integral_pow_two_mul_gaussianReal m
  have hmono := integral_rpow_root_le_of_nonneg_of_le
    (μ := gaussianReal 0 1) (f := fun z : ℝ => |z|)
    (by fun_prop) (fun z => abs_nonneg z) (show 0 < 2 * (m : ℝ) by positivity) hmp
    (integrable_abs_rpow_gaussianReal p hp0.le)
  rw [hscalar] at hmono
  have hleft : Real.sqrt p / 4 ≤ Real.sqrt ((m : ℝ) / 4) := by
    have hh := Real.sqrt_le_sqrt (show p / 16 ≤ (m : ℝ) / 4 by linarith)
    have heq : Real.sqrt (p / 16) = Real.sqrt p / 4 := by
      rw [Real.sqrt_div hp0.le]
      rw [show Real.sqrt (16 : ℝ) = 4 by
        apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
        norm_num]
    rwa [heq] at hh
  exact hleft.trans ((sqrt_div_four_le_even_moment_root m hm).trans hmono)

end NLAlib
