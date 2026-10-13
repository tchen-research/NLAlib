import NLAlib.Polynomial.Chebyshev.Markov
import NLAlib.Polynomial.FunctionApproximation.Approximation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Real.Sign

/-!
# Degree lower bounds for scalar approximation

The endpoint and residual arguments in the operator derivations §7 give
`exp-approx-lower-bound`, `sign-approx-lower-bound`, and
`inverse-approx-lower-bound` from the existing Markov, Bernstein and minimax bounds.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Set Real

namespace NLAlib

/-- Approximating `exp(-x)` on `[0,b]` forces the exact Markov degree lower bound.
Source: Sachdeva–Vishnoi (2014), §4; operator derivations §7.
atlas: exp-approx-lower-bound -/
theorem sq_degree_ge_of_abs_eval_sub_exp_neg_le {p : ℝ[X]} {q : ℕ} {b δ : ℝ}
    (hb : 1 ≤ b) (hδ : 0 ≤ δ) (hp : p.degree ≤ q)
    (herr : ∀ x ∈ Icc 0 b, |p.eval x - exp (-x)| ≤ δ) :
    (1 - exp (-1) - 2 * δ) * b / (2 * (1 + δ)) ≤ (q : ℝ) ^ 2 := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hzero := (abs_le.mp (herr 0 ⟨le_rfl, hbpos.le⟩)).1
  have hone := (abs_le.mp (herr 1 ⟨zero_le_one, hb⟩)).2
  simp only [neg_zero, exp_zero] at hzero
  have hM : ∀ x ∈ Icc 0 b, |p.eval x| ≤ 1 + δ := by
    intro x hx
    have hexp : exp (-x) ≤ 1 := exp_le_one_iff.mpr (by linarith [hx.1])
    calc |p.eval x| = |(p.eval x - exp (-x)) + exp (-x)| := by congr 1; ring
      _ ≤ |p.eval x - exp (-x)| + |exp (-x)| := abs_add_le _ _
      _ ≤ δ + 1 := add_le_add (herr x hx) (by rwa [abs_of_pos (exp_pos _)])
      _ = 1 + δ := add_comm _ _
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope
    (fun x => p.eval x) (fun x => p.derivative.eval x) zero_lt_one p.continuous.continuousOn
    (fun x _ => p.hasDerivAt x)
  simp only [sub_zero, div_one] at hslope
  have hmark := abs_eval_derivative_le_two_mul_sq_div_mul_of_forall_abs_eval_le
    hbpos hp hM (x := ξ) ⟨hξ.1.le, hξ.2.le.trans hb⟩
  have hsep : 1 - exp (-1) - 2 * δ ≤ |p.derivative.eval ξ| := by
    rw [hslope]
    linarith [neg_le_abs (p.eval 1 - p.eval 0)]
  have hbound := hsep.trans hmark
  rw [div_mul_eq_mul_div, sub_zero, le_div_iff₀ hbpos] at hbound
  rw [div_le_iff₀ (by positivity : 0 < 2 * (1 + δ))]
  nlinarith

/-- Error at most `1/8` for `exp(-x)` on `[0,b]`, `b≥1`, requires degree at least `√(b/6)`.
Source: Sachdeva–Vishnoi (2014), §4; operator derivations §7.
atlas: exp-approx-lower-bound -/
theorem sqrt_div_six_le_degree_of_abs_eval_sub_exp_neg_le {p : ℝ[X]} {q : ℕ} {b δ : ℝ}
    (hb : 1 ≤ b) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 8) (hp : p.degree ≤ q)
    (herr : ∀ x ∈ Icc 0 b, |p.eval x - exp (-x)| ≤ δ) :
    √(b / 6) ≤ (q : ℝ) := by
  have hexp : exp (-1) ≤ 3 / 8 := by
    rw [exp_neg, ← one_div, div_le_iff₀ (exp_pos 1)]
    linarith [Real.exp_one_gt_d9]
  have hlower := sq_degree_ge_of_abs_eval_sub_exp_neg_le hb hδ hp herr
  have hratio : b / 6 ≤ (1 - exp (-1) - 2 * δ) * b / (2 * (1 + δ)) := by
    rw [le_div_iff₀ (by positivity : 0 < 2 * (1 + δ))]
    have : 0 ≤ b := by linarith
    nlinarith
  have hs := sq_sqrt (show 0 ≤ b / 6 by positivity)
  nlinarith [hratio.trans hlower, sqrt_nonneg (b / 6), (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]

/-- A polynomial bounded by `M` on the full interval and approximating sign on
the two outer intervals satisfies the sharp Bernstein degree obstruction.
Source: Sachdeva–Vishnoi (2014), sign approximation lower bound;
operator derivations §7. The bound on the full interval is explicit.
atlas: sign-approx-lower-bound -/
theorem degree_mul_bound_ge_of_abs_eval_sub_sign_le {p : ℝ[X]} {q : ℕ} {γ ε M : ℝ}
    (hγ : 0 < γ) (hγone : γ < 1) (hε : ε < 1) (hp : p.degree ≤ q)
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M)
    (herr : ∀ x : ℝ, γ ≤ |x| → |x| ≤ 1 → |p.eval x - Real.sign x| ≤ ε) :
    (1 - ε) * √(1 - γ ^ 2) / γ ≤ (q : ℝ) * M := by
  have hpos := abs_le.mp (herr γ (by rw [abs_of_pos hγ])
    (by rw [abs_of_pos hγ]; exact hγone.le))
  have hneg := abs_le.mp (herr (-γ) (by rw [abs_neg, abs_of_pos hγ])
    (by rw [abs_neg, abs_of_pos hγ]; exact hγone.le))
  rw [sign_of_pos hγ] at hpos
  rw [sign_of_neg (neg_lt_zero.mpr hγ)] at hneg
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope
    (fun x => p.eval x) (fun x => p.derivative.eval x) (show -γ < γ by linarith)
    p.continuous.continuousOn (fun x _ => p.hasDerivAt x)
  have hξabs : |ξ| < γ := abs_lt.mpr hξ
  have hξone : |ξ| < 1 := hξabs.trans hγone
  have hder : (1 - ε) / γ ≤ p.derivative.eval ξ := by
    rw [hslope, le_div_iff₀ (by linarith : 0 < γ - -γ), div_mul_eq_mul_div,
      div_le_iff₀ hγ]
    nlinarith [hpos.1, hneg.2]
  have hbern := abs_eval_derivative_le_div_sqrt_of_forall_abs_eval_le hp hM hξone
  have hroot : 0 < √(1 - ξ ^ 2) := by
    apply sqrt_pos.mpr
    nlinarith [sq_abs ξ, abs_nonneg ξ]
  rw [le_div_iff₀ hroot] at hbern
  have hsqrt : √(1 - γ ^ 2) ≤ √(1 - ξ ^ 2) := by
    apply sqrt_le_sqrt
    nlinarith [sq_abs ξ, abs_nonneg ξ]
  calc (1 - ε) * √(1 - γ ^ 2) / γ = ((1 - ε) / γ) * √(1 - γ ^ 2) := by ring
    _ ≤ ((1 - ε) / γ) * √(1 - ξ ^ 2) := mul_le_mul_of_nonneg_left hsqrt
      (div_nonneg (sub_pos.mpr hε).le hγ.le)
    _ ≤ |p.derivative.eval ξ| * √(1 - ξ ^ 2) :=
      mul_le_mul_of_nonneg_right (hder.trans (le_abs_self _)) (sqrt_nonneg _)
    _ ≤ (q : ℝ) * M := hbern

/-- Approximation of `1/x` gives a residual polynomial, so its error is bounded
below by the reciprocal Chebyshev minimax value divided by `b`.
Source: Golub–Meurant (2010), Ch. 8; operator derivations §7.
atlas: inverse-approx-lower-bound -/
theorem inv_mul_eval_T_le_of_abs_eval_sub_inv_le {a b ε : ℝ} {q : ℕ} {p : ℝ[X]}
    (ha : 0 < a) (hab : a < b) (hp : p.degree < q)
    (herr : ∀ x ∈ Icc a b, |p.eval x - 1 / x| ≤ ε) :
    1 / (b * (T ℝ q).eval ((b + a) / (b - a))) ≤ ε := by
  have hb : 0 < b := ha.trans hab
  have hε : 0 ≤ ε := (abs_nonneg _).trans (herr a ⟨le_rfl, hab.le⟩)
  let r : ℝ[X] := 1 - X * p
  have hr : r.degree ≤ q := by
    by_cases hp0 : p = 0
    · simp [r, hp0]
    · have hpn : p.natDegree < q := by
        rw [degree_eq_natDegree hp0] at hp
        exact_mod_cast hp
      apply degree_le_of_natDegree_le
      refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      exact natDegree_mul_le.trans (by simp only [natDegree_X]; omega)
  have hr0 : r.eval 0 = 1 := by simp [r]
  have hrbound : ∀ x ∈ Icc a b, |r.eval x| ≤ b * ε := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    have heq : r.eval x = -(x * (p.eval x - 1 / x)) := by
      simp only [r, eval_sub, eval_one, eval_mul, eval_X]
      field_simp
      ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hxpos]
    exact (mul_le_mul_of_nonneg_left (herr x hx) hxpos.le).trans
      (mul_le_mul_of_nonneg_right hx.2 hε)
  have hmin := inv_eval_T_real_le_of_forall_abs_eval_le ha hab hr hr0 hrbound
  calc 1 / (b * (T ℝ q).eval ((b + a) / (b - a))) =
        (1 / (T ℝ q).eval ((b + a) / (b - a))) / b := by ring
    _ ≤ ε := (div_le_iff₀ hb).mpr (by simpa [mul_comm] using hmin)

/-- The inverse approximation obstruction also has the explicit condition-number form.
Source: Golub–Meurant (2010), Ch. 8; operator derivations §7.
atlas: inverse-approx-lower-bound -/
theorem sqrt_ratio_pow_div_le_of_abs_eval_sub_inv_le {a b ε : ℝ} {q : ℕ} {p : ℝ[X]}
    (ha : 0 < a) (hab : a < b) (hp : p.degree < q)
    (herr : ∀ x ∈ Icc a b, |p.eval x - 1 / x| ≤ ε) :
    ((√b - √a) / (√b + √a)) ^ q / b ≤ ε := by
  have hTpos : 0 < (T ℝ q).eval ((b + a) / (b - a)) := by
    have harg : 1 ≤ (b + a) / (b - a) := by
      rw [le_div_iff₀ (sub_pos.mpr hab)]
      linarith
    linarith [one_le_eval_T_real (q : ℤ) harg]
  have hsup := eval_T_real_le_pow (q := q)
    (show 1 ≤ (b + a) / (b - a) by rw [le_div_iff₀ (sub_pos.mpr hab)]; linarith)
  rw [add_div_sub_add_sqrt_sq_sub_one_eq ha hab] at hsup
  have hρ : 0 < (√b + √a) / (√b - √a) := by
    have := sqrt_lt_sqrt ha.le hab
    positivity
  have hinv : ((√b - √a) / (√b + √a)) ^ q =
      (((√b + √a) / (√b - √a)) ^ q)⁻¹ := by rw [← inv_pow, inv_div]
  have hle : ((√b - √a) / (√b + √a)) ^ q ≤
      1 / (T ℝ q).eval ((b + a) / (b - a)) := by
    rw [hinv, one_div]
    exact inv_anti₀ hTpos hsup
  calc _ ≤ (1 / (T ℝ q).eval ((b + a) / (b - a))) / b :=
        div_le_div_of_nonneg_right hle (ha.le.trans hab.le)
    _ = 1 / (b * (T ℝ q).eval ((b + a) / (b - a))) := by ring
    _ ≤ ε := inv_mul_eval_T_le_of_abs_eval_sub_inv_le ha hab hp herr

end NLAlib
