import NLAlib.Polynomial.BestApproximation.DoubleResolventPositiveHalfLine
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Converting the explicit exponential denominator to uniform reciprocal error

The approximation cutoff is chosen from the actual smoothing error, independently
of the algebraic positivity cutoff. Source: focused reciprocal reroute, Section 1.
-/

noncomputable section
open Polynomial Set
namespace NLAlib

private theorem abs_inv_sub_inv_le_of_relative_error {f h δ : ℝ}
    (hf : 0 < f) (hh : 0 < h) (hδ : 0 ≤ δ)
    (herr : |f-h| ≤ δ*f^2) (hsmall : δ*f ≤ 1/2) :
    |f⁻¹-h⁻¹| ≤ 2*δ := by
  have hhalf : f/2 ≤ h := by
    have habs := le_abs_self (f-h)
    have := mul_le_mul_of_nonneg_right hsmall hf.le
    nlinarith
  have heq : |f⁻¹-h⁻¹| = |f-h|/(f*h) := by
    rw [show f⁻¹-h⁻¹ = -(f-h)/(f*h) by field_simp; ring]
    rw [abs_div, abs_neg, abs_mul, abs_of_pos hf, abs_of_pos hh]
  rw [heq, div_le_iff₀ (mul_pos hf hh)]
  have := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hδ hf.le)
  nlinarith

/-- A globally positive increasing polynomial with the smoothing value bound
has uniform reciprocal error at most four times its smoothing coefficient.
The cutoff is proved to exist and the two interval estimates are explicit.
Source: focused reciprocal reroute, compact interval and tail comparison. -/
theorem abs_exp_neg_quarter_sub_inv_eval_le_of_value_bound
    (p : ℝ[X]) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1/2)
    (hp : ∀ x : ℝ, 0 ≤ x → 0 < p.eval x)
    (hmono : MonotoneOn p.eval (Ici 0))
    (herr : ∀ x : ℝ, 0 ≤ x →
      |Real.exp (x/4)-p.eval x| ≤ δ*Real.exp (x/2))
    {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (-x/4) - (p.eval x)⁻¹| ≤ 4*δ := by
  let a : ℝ := -4*Real.log (2*δ)
  have h2δ : 0 < 2*δ := by positivity
  have ha : 0 < a := by
    have := Real.log_neg h2δ (by linarith : 2*δ < 1)
    dsimp [a]
    linarith
  have hea : Real.exp (a/4) = (2*δ)⁻¹ := by
    rw [show a/4 = -Real.log (2*δ) by dsimp [a]; ring,
      Real.exp_neg, Real.exp_log h2δ]
  have heneg (y : ℝ) : Real.exp (-y/4) = (Real.exp (y/4))⁻¹ := by
    rw [show -y/4 = -(y/4) by ring, Real.exp_neg]
  have hehalf (y : ℝ) : Real.exp (y/2) = (Real.exp (y/4))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hlocal (y : ℝ) (hy : 0 ≤ y) (hya : y ≤ a) :
      |Real.exp (-y/4)-(p.eval y)⁻¹| ≤ 2*δ := by
    rw [heneg]
    apply abs_inv_sub_inv_le_of_relative_error (Real.exp_pos _) (hp y hy) hδ.le
    · simpa only [hehalf] using herr y hy
    · have hle : Real.exp (y/4) ≤ (2*δ)⁻¹ := by
        rw [← hea]
        exact Real.exp_le_exp.mpr (by linarith)
      have := mul_le_mul_of_nonneg_left hle hδ.le
      have heq : δ*(2*δ)⁻¹ = (1/2:ℝ) := by field_simp
      rwa [heq] at this
  by_cases hxa : x ≤ a
  · exact (hlocal x hx hxa).trans (by linarith)
  · have hax : a ≤ x := le_of_not_ge hxa
    have haerror := herr a ha.le
    rw [hehalf, hea] at haerror
    have haabs := le_abs_self ((2*δ)⁻¹-p.eval a)
    have hhalf : (2*δ)⁻¹/2 ≤ p.eval a := by
      have hid : δ*((2*δ)⁻¹)^2 = (2*δ)⁻¹/2 := by field_simp
      rw [hid] at haerror
      linarith
    have hpa : (2*δ)⁻¹/2 ≤ p.eval x :=
      hhalf.trans (hmono ha.le hx hax)
    have hinv : (p.eval x)⁻¹ ≤ 4*δ := by
      have hid : ((2*δ)⁻¹/2)⁻¹ = 4*δ := by field_simp; ring
      rw [← hid]
      exact (inv_le_inv₀ (hp x hx) (by positivity)).mpr hpa
    have he : Real.exp (-x/4) ≤ 2*δ := by
      calc
        _ ≤ Real.exp (-a/4) := Real.exp_le_exp.mpr (by linarith)
        _ = 2*δ := by rw [heneg, hea, inv_inv]
    exact abs_le.mpr ⟨by have := Real.exp_pos (-x/4); linarith,
      by have := inv_pos.mpr (hp x hx); linarith⟩

/-- The explicit reciprocal denominator has degree exactly the advertised order,
including the constant denominator in order zero.
Source: focused reciprocal reroute, explicit denominator.
atlas: exp-rational-halfline (partial) -/
@[simp] theorem natDegree_reciprocalExponentialDenominator (n : ℕ) :
    (reciprocalExponentialDenominator n).natDegree = n := by
  by_cases hn : n=0
  · simp [reciprocalExponentialDenominator, hn]
  · rw [reciprocalExponentialDenominator, if_neg hn, natDegree_comp,
      natDegree_doubleResolventExponentialDenominator,
      natDegree_C_mul (by norm_num : (4:ℝ) ≠ 0), natDegree_X, mul_one]

/-- The actual explicit denominator is positive on the entire half-line.
Its reciprocal therefore has no pole there in every degree.
Source: focused reciprocal reroute, global positivity.
atlas: exp-rational-halfline (partial) -/
theorem reciprocalExponentialDenominator_eval_pos (n : ℕ)
    {x : ℝ} (hx : 0 ≤ x) : 0 < (reciprocalExponentialDenominator n).eval x := by
  by_cases hn : n=0
  · simp [reciprocalExponentialDenominator, hn]
  · simp only [reciprocalExponentialDenominator, if_neg hn, eval_comp, eval_mul,
      eval_C, eval_X]
    exact (doubleResolventExponentialDenominator_pos_halfLine (by omega)
      (show 0 ≤ 4*x by positivity)).1

/-- In every positive degree the explicit reciprocal denominator has positive
derivative on the entire half-line. Source: focused reciprocal reroute.
atlas: exp-rational-halfline (partial) -/
theorem reciprocalExponentialDenominator_derivative_eval_pos {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 0 ≤ x) : 0 < (reciprocalExponentialDenominator n).derivative.eval x := by
  simp only [reciprocalExponentialDenominator, if_neg (by omega : n≠0),
    derivative_comp, derivative_mul, derivative_C, derivative_X, zero_mul,
    zero_add, mul_one, eval_mul, eval_comp, eval_C, eval_X]
  exact mul_pos (by norm_num) ((doubleResolventExponentialDenominator_pos_halfLine hn
    (show 0 ≤ 4*x by positivity)).2)

/-- The actual explicit denominator is strictly increasing throughout the whole
positive half-line in every positive degree.
Source: focused reciprocal reroute, positive denominator and derivative.
atlas: exp-rational-halfline (partial) -/
theorem reciprocalExponentialDenominator_strictMonoOn_halfLine {n : ℕ} (hn : 0<n) :
    StrictMonoOn (reciprocalExponentialDenominator n).eval (Ici 0) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici _)
    (reciprocalExponentialDenominator n).continuous.continuousOn
    (fun x _ => ((reciprocalExponentialDenominator n).hasDerivAt x).hasDerivWithinAt)
  intro x hx
  exact reciprocalExponentialDenominator_derivative_eval_pos hn (interior_subset hx)

private theorem four_smoothingValueConstant_eq :
    4 * Real.sqrt (5/42) = Real.sqrt (40/21) := by
  have h1 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5/42)
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 40/21)
  nlinarith [Real.sqrt_nonneg (5/42), Real.sqrt_nonneg (40/21)]

/-- The finite two-resolvent polynomial gives the stated uniform reciprocal
error bound in every degree. This is the actual pole-free denominator, not a
certificate supplied as a hypothesis. Source: focused reciprocal reroute.
atlas: exp-rational-halfline (partial) -/
theorem abs_exp_neg_sub_inv_reciprocalExponentialDenominator_le (n : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (-x)-((reciprocalExponentialDenominator n).eval x)⁻¹| ≤
      Real.sqrt (40/21) / 3^n := by
  by_cases hn : n=0
  · simp only [reciprocalExponentialDenominator, hn, if_true, eval_one,
      inv_one, pow_zero, div_one]
    have he : Real.exp (-x) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
    have hs : 1 ≤ Real.sqrt (40/21) := by
      have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 40/21)
      nlinarith [Real.sqrt_nonneg (40/21)]
    exact (abs_le.mpr ⟨by have := Real.exp_pos (-x); linarith, by linarith⟩).trans hs
  · let δ : ℝ := Real.sqrt (5/42) / 3^n
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδsmall : δ < 1/2 := by
      have hp : (1:ℝ) ≤ 3^n := one_le_pow₀ (by norm_num)
      have hs : Real.sqrt (5/42) < 1/2 := by
        have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5/42)
        nlinarith [Real.sqrt_nonneg (5/42)]
      have hle : δ ≤ Real.sqrt (5/42) := by
        dsimp [δ]
        apply (div_le_iff₀ (by positivity : (0:ℝ) < 3^n)).mpr
        nlinarith [Real.sqrt_nonneg (5/42)]
      exact hle.trans_lt hs
    have h := abs_exp_neg_quarter_sub_inv_eval_le_of_value_bound
      (doubleResolventExponentialDenominator n) hδ hδsmall
      (fun t ht => (doubleResolventExponentialDenominator_pos_halfLine (by omega) ht).1)
      (doubleResolventExponentialDenominator_monotoneOn_halfLine (by omega))
      (fun t ht => abs_exp_quarter_sub_doubleResolventExponentialDenominator_le n ht)
      (show 0 ≤ 4*x by positivity)
    have hrhs : 4*δ = Real.sqrt (40/21)/3^n := by
      dsimp [δ]
      rw [← mul_div_assoc, four_smoothingValueConstant_eq]
    rw [hrhs, show -(4*x)/4 = -x by ring] at h
    simpa only [reciprocalExponentialDenominator, if_neg hn, eval_comp, eval_mul,
      eval_C, eval_X] using h

/-- The simpler `√2 · 3⁻ⁿ` bound follows from the sharper explicit constant.
Source: focused reciprocal reroute, uniform reciprocal error.
atlas: exp-rational-halfline (partial) -/
theorem abs_exp_neg_sub_inv_reciprocalExponentialDenominator_le_sqrt_two (n : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (-x)-((reciprocalExponentialDenominator n).eval x)⁻¹| ≤
      Real.sqrt 2 / 3^n := by
  apply (abs_exp_neg_sub_inv_reciprocalExponentialDenominator_le n hx).trans
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by norm_num)) (by positivity)

end NLAlib
