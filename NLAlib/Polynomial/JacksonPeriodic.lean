import NLAlib.Polynomial.SawtoothNorm
import NLAlib.ForMathlib.Analysis.Lipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Sharp periodic approximation through the actual sawtooth convolution

Lipschitz functions are absolutely continuous in Mathlib. Integration by parts against
the proved sawtooth error yields the precise `π/(2(n+1))` approximation constant directly.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Real MeasureTheory
open scoped Topology

namespace NLAlib

/-- The fixed periodic approximant obtained by convolving with the actual derivative
polynomial of the sawtooth interpolant, including the mean term.
Source: Arnold, numerical analysis, Section 1.2; operator rederivations `rt:periodic-jackson`.
Atlas `jackson-lipschitz` (construction helper). -/
def jacksonPeriodicApprox (n : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t : ℝ in 0..2 * Real.pi,
    (sawtoothErrorDerivativePolynomial n).eval (cos t) * g (x - t)

/-- The actual unwrapped sawtooth error is smooth, hence absolutely continuous on the
integration interval.
Source: the explicit polynomial-sine construction; helper for sharp `jackson-lipschitz`. -/
theorem absolutelyContinuousOnInterval_sawtoothError (n : ℕ) :
    AbsolutelyContinuousOnInterval (sawtoothError n) 0 (2 * Real.pi) := by
  have hp : ContDiff ℝ 1 (fun x : ℝ => (sawtoothSineInterp n).eval x) := by
    simpa using (sawtoothSineInterp n).contDiff_aeval (𝕜 := ℝ) 1
  have hτ : ContDiff ℝ 1 (sawtoothApprox n) :=
    Real.contDiff_sin.mul (hp.comp Real.contDiff_cos)
  have hB : ContDiff ℝ 1 (fun t : ℝ => Real.pi - t) := contDiff_const.sub contDiff_id
  exact (hB.sub hτ).contDiffOn.absolutelyContinuousOnInterval

/-- Integration by parts gives the exact error of the fixed convolution approximant.
The periodic endpoint contribution is `-2π g(x)` and the polynomial kernel is the actual
negative derivative of the proved sawtooth error.
Source: operator rederivations `rt:periodic-jackson` (`jackson-lipschitz`, helper). -/
theorem sub_jacksonPeriodicApprox_eq_integral {g : ℝ → ℝ} {L : NNReal} (hg : LipschitzWith L g)
    (hper : Function.Periodic g (2 * Real.pi)) (n : ℕ) (x : ℝ) :
    g x - jacksonPeriodicApprox n g x = -(2 * Real.pi)⁻¹ *
      ∫ t : ℝ in 0..2 * Real.pi, sawtoothError n t * deriv (fun s : ℝ => g (x - s)) t := by
  let gx : ℝ → ℝ := fun t => g (x - t)
  have hgx := lipschitzWith_comp_const_sub hg x
  have hgAC : AbsolutelyContinuousOnInterval gx 0 (2 * Real.pi) :=
    hgx.lipschitzOnWith.absolutelyContinuousOnInterval
  have hIB := (absolutelyContinuousOnInterval_sawtoothError n).integral_mul_deriv_eq_deriv_mul hgAC
  have hzero : sawtoothError n 0 = Real.pi := by simp [sawtoothError]
  have hlast : sawtoothError n (2 * Real.pi) = -Real.pi := by
    have h := sawtoothError_two_pi_sub n 0
    simpa only [sub_zero, hzero] using h
  have hgzero : gx 0 = g x := by simp [gx]
  have hglast : gx (2 * Real.pi) = g x := hper.sub_eq x
  rw [hlast, hzero, hgzero, hglast] at hIB
  have hder : ∀ t : ℝ, deriv (sawtoothError n) t =
      -(sawtoothErrorDerivativePolynomial n).eval (cos t) :=
    fun t => (hasDerivAt_sawtoothError n t).deriv
  simp_rw [hder, neg_mul] at hIB
  rw [intervalIntegral.integral_neg] at hIB
  unfold jacksonPeriodicApprox
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := Real.two_pi_pos.ne'
  change g x - (2 * Real.pi)⁻¹ *
    (∫ t in 0..2 * Real.pi, (sawtoothErrorDerivativePolynomial n).eval (cos t) * gx t) =
    -(2 * Real.pi)⁻¹ * (∫ t in 0..2 * Real.pi, sawtoothError n t * deriv gx t)
  field_simp [hπ]
  nlinarith [hIB]

/-- The actual fixed periodic convolution approximant has the exact sharp error constant
`π L/(2(n+1))` for every periodic `L`-Lipschitz real function. All kernel norm and
absolute-continuity inputs are proved rather than assumed.
Source: Arnold, numerical analysis, Section 1.2; operator rederivations `rt:periodic-jackson`.
Atlas `jackson-lipschitz` (periodic error helper). -/
theorem abs_sub_jacksonPeriodicApprox_le {g : ℝ → ℝ} {L : NNReal} (hg : LipschitzWith L g)
    (hper : Function.Periodic g (2 * Real.pi)) (n : ℕ) (x : ℝ) :
    |g x - jacksonPeriodicApprox n g x| ≤ Real.pi * (L : ℝ) / (2 * (n + 1)) := by
  have hgx := lipschitzWith_comp_const_sub hg x
  have hpoint : ∀ t : ℝ,
      ‖sawtoothError n t * deriv (fun s : ℝ => g (x - s)) t‖ ≤ |sawtoothError n t| * (L : ℝ) := by
    intro t
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz hgx) (abs_nonneg _)
  have hbound : IntervalIntegrable (fun t : ℝ => |sawtoothError n t| * (L : ℝ))
      volume 0 (2 * Real.pi) := ((continuous_sawtoothError n).abs.mul continuous_const).intervalIntegrable _ _
  have hI := intervalIntegral.norm_integral_le_of_norm_le Real.two_pi_pos.le
    (ae_of_all volume (fun t _ => hpoint t)) hbound
  rw [intervalIntegral.integral_mul_const] at hI
  rw [sub_jacksonPeriodicApprox_eq_integral hg hper n x, abs_mul, abs_neg,
    abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
  have hh := mul_le_mul_of_nonneg_left hI (show 0 ≤ (2 * Real.pi)⁻¹ by positivity)
  rw [Real.norm_eq_abs] at hh
  refine hh.trans_eq ?_
  rw [integral_abs_sawtoothError_eq]
  field_simp

end NLAlib
