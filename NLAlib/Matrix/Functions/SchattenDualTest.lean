import NLAlib.Matrix.Norms.ComplexSchattenDuality
import NLAlib.Matrix.Norms.SchattenDiagonal
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analytic diagonal tests for Schatten interpolation

Normalized positive singular coefficients are raised to a complex affine
power. Zero coefficients remain identically zero, so singular matrices need
no regularization to construct their analytic dual tests.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Appendix D.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- One coefficient of the analytic Schatten dual test. The positive branch
is entire in `z`; a zero singular direction contributes the zero function. -/
def schattenDualTestCoefficient (r p w : ℝ) (z : ℂ) : ℂ :=
  if 0 < w then Complex.exp (((p : ℂ) - z) / (r : ℂ) * (Real.log w : ℂ)) else 0

/-- Each fixed singular direction gives an entire analytic test coefficient. -/
@[fun_prop] theorem differentiable_schattenDualTestCoefficient (r p w : ℝ) :
    Differentiable ℂ (schattenDualTestCoefficient r p w) := by
  unfold schattenDualTestCoefficient
  split_ifs
  · fun_prop
  · exact differentiable_const _

/-- The analytic test coefficient is continuous, also for a zero singular
coefficient. -/
@[fun_prop] theorem continuous_schattenDualTestCoefficient (r p w : ℝ) :
    Continuous (schattenDualTestCoefficient r p w) :=
  (differentiable_schattenDualTestCoefficient r p w).continuous

/-- The modulus of a positive analytic test coefficient is its real power
at the real coordinate of the strip. -/
theorem norm_schattenDualTestCoefficient_of_pos {w : ℝ} (hw : 0 < w)
    (r p : ℝ) (z : ℂ) :
    ‖schattenDualTestCoefficient r p w z‖ = w ^ ((p - z.re) / r) := by
  rw [schattenDualTestCoefficient, if_pos hw, Complex.norm_exp, Real.rpow_def_of_pos hw]
  congr 1
  simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero, mul_zero]
  ring

/-- Every normalized singular coefficient has test modulus at most one on
any point to the left of the strip's right boundary. -/
theorem norm_schattenDualTestCoefficient_le_one {r p w : ℝ}
    (hr : 0 < r) (hp : 1 ≤ p) (hw : w ∈ Set.Icc (0 : ℝ) 1)
    {z : ℂ} (hz : z.re ≤ 1) : ‖schattenDualTestCoefficient r p w z‖ ≤ 1 := by
  by_cases hwpos : 0 < w
  · rw [norm_schattenDualTestCoefficient_of_pos hwpos]
    exact Real.rpow_le_one hw.1 hw.2 (div_nonneg (by linarith) hr.le)
  · simp only [schattenDualTestCoefficient, if_neg hwpos, norm_zero, zero_le_one]

/-- On the left boundary the modulus is the normalized source power,
including zero singular directions. -/
theorem norm_schattenDualTestCoefficient_left {r p w : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hw : 0 ≤ w) (t : ℝ) :
    ‖schattenDualTestCoefficient r p w ((t : ℂ) * Complex.I)‖ = w ^ (p / r) := by
  by_cases hwpos : 0 < w
  · rw [norm_schattenDualTestCoefficient_of_pos hwpos]
    simp
  · have hwzero : w = 0 := le_antisymm (not_lt.mp hwpos) hw
    subst w
    simp [schattenDualTestCoefficient, Real.zero_rpow (div_pos hp hr).ne']

/-- At the interpolation point the coefficient is the ordinary real dual
power, with its zero convention justified by the positive exponent. -/
theorem schattenDualTestCoefficient_center {r p w : ℝ}
    (hr : 0 < r) (hpr : r < p) (hw : 0 ≤ w) :
    schattenDualTestCoefficient r p w (r : ℂ) = ((w ^ (p / r - 1) : ℝ) : ℂ) := by
  by_cases hwpos : 0 < w
  · rw [schattenDualTestCoefficient, if_pos hwpos, Real.rpow_def_of_pos hwpos,
      Complex.ofReal_exp]
    congr 1
    push_cast
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp [hrC]
  · have hwzero : w = 0 := le_antisymm (not_lt.mp hwpos) hw
    subst w
    have hexp : 0 < p / r - 1 := by rw [sub_pos, one_lt_div hr]; exact hpr
    simp [schattenDualTestCoefficient, Real.zero_rpow hexp.ne']

/-- On the right boundary, raising the modulus to the conjugate exponent
reproduces the left-boundary power sum. -/
theorem norm_schattenDualTestCoefficient_right_rpow {r p q w : ℝ}
    (hr : 0 < r) (hpq : Real.HolderConjugate p q) (hw : 0 ≤ w) (t : ℝ) :
    ‖schattenDualTestCoefficient r p w (1 + (t : ℂ) * Complex.I)‖ ^ q = w ^ (p / r) := by
  by_cases hwpos : 0 < w
  · rw [norm_schattenDualTestCoefficient_of_pos hwpos]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
    rw [← Real.rpow_mul hw]
    congr 1
    have heq := hpq.sub_one_mul_conj
    field_simp
    nlinarith
  · have hwzero : w = 0 := le_antisymm (not_lt.mp hwpos) hw
    subst w
    simp [schattenDualTestCoefficient, Real.zero_rpow hpq.symm.ne_zero,
      Real.zero_rpow (div_pos hpq.pos hr).ne']

end NLAlib
