import NLAlib.Polynomial.FunctionApproximation.Basic
import NLAlib.Polynomial.FunctionApproximation.EllipseGeometry
import NLAlib.Polynomial.FunctionApproximation.AnalyticApproximation
import NLAlib.Polynomial.Chebyshev.Growth
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Approximation of functions analytic in the right half-plane

An explicit Bernstein ellipse enclosure supplies polynomial approximation on a
positive interval. Realises `slit-plane-analytic-approx`.
-/

noncomputable section

open Complex Polynomial Polynomial.Chebyshev Set Real

namespace NLAlib

/-- A Bernstein radius below the inverse-approximation threshold has a positive
transplanted ellipse lower bound.
Source: Trefethen, ATAP, Ch. 8; operator derivations §6.
atlas: slit-plane-analytic-approx -/
theorem bernsteinIntervalLower_pos {a b ρ : ℝ} (ha : 0 < a) (hab : a < b)
    (hρ : 1 < ρ) (hr : ρ < (√b + √a) / (√b - √a)) :
    0 < bernsteinIntervalLower a b ρ := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have harg : 1 ≤ (b + a) / (b - a) := by rw [le_div_iff₀ hba]; linarith
  have hs : 1 < (√b + √a) / (√b - √a) := by
    have hsa := sqrt_pos.mpr ha
    have hsb := sqrt_lt_sqrt ha.le hab
    rw [lt_div_iff₀ (by linarith : 0 < √b - √a)]
    linarith
  have hiden : (√b + √a) / (√b - √a) + ((√b + √a) / (√b - √a))⁻¹ =
      2 * ((b + a) / (b - a)) := by
    rw [← add_div_sub_add_sqrt_sq_sub_one_eq ha hab,
      Real.add_sqrt_self_sq_sub_one_inv harg]
    ring
  have hcmp := strictMonoOn_add_inv_Ici_one (𝕜 := ℝ) hρ.le hs.le hr
  dsimp only at hcmp
  rw [hiden] at hcmp
  have hh : (ρ + ρ⁻¹) * (b - a) < 2 * (b + a) := by
    rwa [← mul_div_assoc, lt_div_iff₀ hba] at hcmp
  dsimp [bernsteinIntervalLower]
  linarith

/-- The affine Bernstein ellipse stays in its explicit real-part and modulus enclosure.
Source: Trefethen, ATAP, Ch. 8; operator derivations §6.
Helper for `slit-plane-analytic-approx`. -/
theorem bernsteinIntervalMap_mem_enclosure {a b ρ : ℝ} (ha : 0 < a) (hab : a < b)
    (hρ : 1 < ρ) {z : ℂ} (hz : z ∈ openBernsteinEllipse ρ) :
    bernsteinIntervalLower a b ρ ≤ (bernsteinIntervalMap a b z).re ∧
      ‖bernsteinIntervalMap a b z‖ ≤ bernsteinIntervalUpper a b ρ := by
  have hfilled := (mem_filledBernsteinEllipse_iff hρ.le z).mpr
    ((mem_openBernsteinEllipse_iff hρ z).mp hz).le
  constructor
  · simpa [bernsteinIntervalLower, bernsteinIntervalMap, Complex.div_re] using
      re_affine_ge_of_mem_filledBernsteinEllipse hab.le hρ.le hfilled
  · have hsum : 0 ≤ b + a := by linarith
    simpa only [bernsteinIntervalMap, bernsteinIntervalUpper, abs_of_nonneg hsum] using
      norm_affine_le_of_mem_filledBernsteinEllipse hab.le hρ.le hfilled

/-- A function holomorphic in the right half-plane, bounded on the explicit ellipse
enclosure, admits a real polynomial with the exact Bernstein rate on `[a,b]`.
Source: Trefethen, ATAP, Thm 8.2; operator derivations §6.
atlas: slit-plane-analytic-approx -/
theorem exists_degree_le_abs_sub_eval_le_of_rightHalfPlane
    {a b ρ M : ℝ} {f : ℝ → ℝ} {F : ℂ → ℂ}
    (ha : 0 < a) (hab : a < b) (hρ : 1 < ρ)
    (hr : ρ < (√b + √a) / (√b - √a))
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.re})
    (hM : ∀ z : ℂ, bernsteinIntervalLower a b ρ ≤ z.re →
      ‖z‖ ≤ bernsteinIntervalUpper a b ρ → ‖F z‖ ≤ M)
    (hmatch : ∀ x ∈ Icc a b, F x = (f x : ℂ)) (n : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ x ∈ Icc a b,
      |f x - p.eval x| ≤ 2 * M / ρ ^ n / (ρ - 1) := by
  have hlower := bernsteinIntervalLower_pos ha hab hρ hr
  have hmaps : MapsTo (bernsteinIntervalMap a b) (openBernsteinEllipse ρ)
      {z : ℂ | 0 < z.re} := by
    intro z hz
    exact hlower.trans_le (bernsteinIntervalMap_mem_enclosure ha hab hρ hz).1
  have hdiff : Differentiable ℂ (bernsteinIntervalMap a b) := by
    unfold bernsteinIntervalMap
    fun_prop
  refine exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse_interval hab hρ
    (hF.comp hdiff.differentiableOn hmaps) ?_ ?_ n
  · intro z hz
    obtain ⟨hl, hu⟩ := bernsteinIntervalMap_mem_enclosure ha hab hρ hz
    exact hM _ hl hu
  · intro t ht
    have hreal : bernsteinIntervalMap a b (t : ℂ) =
        (((b - a) * t + b + a) / 2 : ℝ) := by
      dsimp [bernsteinIntervalMap]
      push_cast
      ring
    simp only [Function.comp_apply, hreal]
    apply hmatch
    constructor <;> nlinarith [ht.1, ht.2]

/-- Principal real powers have the stated enclosure bound on a right-half-plane ellipse.
Source: Trefethen, ATAP, Ch. 8; operator derivations §6.
atlas: slit-plane-analytic-approx -/
theorem exists_degree_le_abs_rpow_sub_eval_le {a b ρ : ℝ}
    (ha : 0 < a) (hab : a < b) (hρ : 1 < ρ)
    (hr : ρ < (√b + √a) / (√b - √a)) (α : ℝ) (n : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ x ∈ Icc a b,
      |x ^ α - p.eval x| ≤
        2 * max ((bernsteinIntervalLower a b ρ) ^ α)
          ((bernsteinIntervalUpper a b ρ) ^ α) / ρ ^ n / (ρ - 1) := by
  have hlower := bernsteinIntervalLower_pos ha hab hρ hr
  apply exists_degree_le_abs_sub_eval_le_of_rightHalfPlane
    (F := fun z : ℂ => z ^ (α : ℂ)) ha hab hρ hr
  · intro z hz
    exact (Complex.hasStrictDerivAt_cpow_const (c := (α : ℂ))
      (Or.inl hz : z ∈ Complex.slitPlane)).hasDerivAt.differentiableAt.differentiableWithinAt
  · intro z hl hu
    have hlnorm : bernsteinIntervalLower a b ρ ≤ ‖z‖ := hl.trans (Complex.re_le_norm z)
    rw [Complex.norm_cpow_real]
    rcases le_total 0 α with hα | hα
    · exact (Real.rpow_le_rpow (by positivity) hu hα).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hlower hlnorm hα).trans (le_max_left _ _)
  · intro x hx
    exact (Complex.ofReal_cpow (ha.le.trans hx.1) α).symm

/-- The principal logarithm has the stated enclosure bound on a right-half-plane ellipse.
Source: Trefethen, ATAP, Ch. 8; operator derivations §6.
atlas: slit-plane-analytic-approx -/
theorem exists_degree_le_abs_log_sub_eval_le {a b ρ : ℝ}
    (ha : 0 < a) (hab : a < b) (hρ : 1 < ρ)
    (hr : ρ < (√b + √a) / (√b - √a)) (n : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ x ∈ Icc a b,
      |Real.log x - p.eval x| ≤
        2 * (max |Real.log (bernsteinIntervalLower a b ρ)|
          |Real.log (bernsteinIntervalUpper a b ρ)| + Real.pi / 2) / ρ ^ n / (ρ - 1) := by
  have hlower := bernsteinIntervalLower_pos ha hab hρ hr
  apply exists_degree_le_abs_sub_eval_le_of_rightHalfPlane
    (F := Complex.log) ha hab hρ hr
  · intro z hz
    exact (Complex.differentiableAt_log (Or.inl hz : z ∈ Complex.slitPlane)).differentiableWithinAt
  · intro z hl hu
    have hlnorm : bernsteinIntervalLower a b ρ ≤ ‖z‖ := hl.trans (Complex.re_le_norm z)
    have hnpos : 0 < ‖z‖ := hlower.trans_le hlnorm
    have hloglo := Real.log_le_log hlower hlnorm
    have hloghi := Real.log_le_log hnpos hu
    have hlogabs : |Real.log ‖z‖| ≤ max |Real.log (bernsteinIntervalLower a b ρ)|
        |Real.log (bernsteinIntervalUpper a b ρ)| := by
      rw [abs_le]
      constructor
      · have hm := le_max_left |Real.log (bernsteinIntervalLower a b ρ)|
          |Real.log (bernsteinIntervalUpper a b ρ)|
        linarith [neg_le_abs (Real.log (bernsteinIntervalLower a b ρ))]
      · exact hloghi.trans ((le_abs_self _).trans (le_max_right _ _))
    have harg : |Complex.arg z| ≤ Real.pi / 2 :=
      Complex.abs_arg_le_pi_div_two_iff.mpr (hlower.le.trans hl)
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
      rw [Complex.log_re, Complex.log_im]
      exact add_le_add hlogabs harg)
  · intro x hx
    exact (Complex.ofReal_log (ha.le.trans hx.1)).symm

end NLAlib
