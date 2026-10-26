import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Explicit constants for local Rayleigh quotient iteration

Scalar inequalities used after the Hermitian spectral decomposition. The variable `q`
denotes the squared tangent to the target eigenvector line and `e` the absolute Rayleigh
quotient error. These lemmas do not assert realization by a matrix iteration.

Source: Trefethen–Bau (1997), Lecture 27; the explicit constants follow the finite spectral
estimate in the accompanying RQI card.
-/

namespace NLAlib.RayleighQuotientIteration

/-- In the stated local neighborhood the Rayleigh error is at most one quarter of the gap.
This scalar estimate is a helper for `rayleigh-quotient-iteration`. -/
theorem error_le_gap_div_four {g M q e : ℝ} (_hg : 0 < g) (hM : 0 < M)
    (hq : 0 ≤ q) (hlocal : q ≤ g / (4 * M))
    (he : e ≤ M * q / (1 + q)) : e ≤ g / 4 := by
  have hden : 0 < 1 + q := by positivity
  have hMq : M * q ≤ g / 4 := by
    have h := (le_div_iff₀ (show 0 < 4 * M by positivity)).mp hlocal
    nlinarith
  have hfrac : M * q / (1 + q) ≤ M * q := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (mul_nonneg hM.le hq) hq]
  exact he.trans (hfrac.trans hMq)

/-- The one-step spectral fraction is at most `2 e / g` in the local neighborhood.
Helper for `rayleigh-quotient-iteration`. -/
theorem error_div_gap_sub_le {g e : ℝ} (hg : 0 < g) (he : 0 ≤ e)
    (heg : e ≤ g / 4) : e / (g - e) ≤ 2 * e / g := by
  have hge : 0 < g - e := by linarith
  apply (div_le_div_iff₀ hge hg).2
  nlinarith [mul_nonneg he (show 0 ≤ g - 2 * e by linarith)]

/-- Cubic contraction of the squared tangent, with the stated explicit constants, from
the finite spectral estimate. Helper for `rayleigh-quotient-iteration`. -/
theorem tangent_sq_cubic_le {g M q e q' : ℝ} (hg : 0 < g) (hM : 0 < M)
    (hq : 0 ≤ q) (he : 0 ≤ e) (hlocal : q ≤ g / (4 * M))
    (herr : e ≤ M * q / (1 + q))
    (hstep : q' ≤ (e / (g - e)) ^ 2 * q) :
    q' ≤ (2 * M / g) ^ 2 * q ^ 3 ∧ q' ≤ q / 4 := by
  have heg := error_le_gap_div_four hg hM hq hlocal herr
  have hfrac := error_div_gap_sub_le hg he heg
  have hden : 0 < 1 + q := by positivity
  have heMq : e ≤ M * q := by
    apply herr.trans
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (mul_nonneg hM.le hq) hq]
  have hratio : e / (g - e) ≤ 2 * M / g * q := by
    apply hfrac.trans
    calc
      2 * e / g ≤ 2 * (M * q) / g := div_le_div_of_nonneg_right (by linarith) hg.le
      _ = 2 * M / g * q := by ring
  have hge : 0 < g - e := by linarith
  have hcubic : q' ≤ (2 * M / g) ^ 2 * q ^ 3 := by
    calc
      q' ≤ (e / (g - e)) ^ 2 * q := hstep
      _ ≤ (2 * M / g * q) ^ 2 * q :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hratio 2) hq
      _ = (2 * M / g) ^ 2 * q ^ 3 := by ring
  have hsmall : 2 * M / g * q ≤ 1 / 2 := by
    have h := (le_div_iff₀ (show 0 < 4 * M by positivity)).mp hlocal
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_le_iff₀ hg).2
    nlinarith
  refine ⟨hcubic, ?_⟩
  calc
    q' ≤ (2 * M / g * q) ^ 2 * q := by nlinarith [hcubic]
    _ ≤ (1 / 2 : ℝ) ^ 2 * q :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hsmall 2) hq
    _ = q / 4 := by ring

/-- The Rayleigh error after a step is sixth order in the incoming tangent.
Helper for `rayleigh-quotient-iteration`. -/
theorem error_le_tangent_sq_cube {g M q q' e' : ℝ} (hM : 0 ≤ M)
    (hstep : q' ≤ (2 * M / g) ^ 2 * q ^ 3) (herr : e' ≤ M * q') :
    e' ≤ (4 * M ^ 3 / g ^ 2) * q ^ 3 := by
  calc
    e' ≤ M * q' := herr
    _ ≤ M * ((2 * M / g) ^ 2 * q ^ 3) := mul_le_mul_of_nonneg_left hstep hM
    _ = (4 * M ^ 3 / g ^ 2) * q ^ 3 := by ring

/-- At an extremal eigenvalue the lower Rayleigh error bound turns the angle contraction
into scalar cubic convergence with constant `8 M / g³`. This is a scalar helper; the
matrix theorem must establish the extremal spectral lower bound. -/
theorem error_step_le_cube {g M q e q' e' : ℝ} (hg : 0 < g) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (he : 0 ≤ e) (hqone : q ≤ 1) (heg : e ≤ g / 4)
    (hlower : g * q / (1 + q) ≤ e)
    (hstep : q' ≤ (e / (g - e)) ^ 2 * q) (herr : e' ≤ M * q') :
    e' ≤ (8 * M / g ^ 3) * e ^ 3 := by
  have hqbound : q ≤ 2 * e / g := by
    have hlow := (div_le_iff₀ (show 0 < 1 + q by positivity)).mp hlower
    apply (le_div_iff₀ hg).2
    nlinarith [mul_le_mul_of_nonneg_left hqone he]
  have hge : 0 < g - e := by linarith
  have hfrac := error_div_gap_sub_le hg he heg
  calc
    e' ≤ M * q' := herr
    _ ≤ M * ((e / (g - e)) ^ 2 * q) := mul_le_mul_of_nonneg_left hstep hM
    _ ≤ M * ((2 * e / g) ^ 2 * q) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfrac 2) hq) hM
    _ ≤ M * ((2 * e / g) ^ 2 * (2 * e / g)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hqbound (sq_nonneg _)) hM
    _ = (8 * M / g ^ 3) * e ^ 3 := by ring

end NLAlib.RayleighQuotientIteration
