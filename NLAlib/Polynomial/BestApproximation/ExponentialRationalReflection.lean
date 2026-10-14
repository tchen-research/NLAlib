import NLAlib.Polynomial.BestApproximation.ExponentialReciprocalRootLimit

/-!
# Reflection of the actual half-line exponential minimax problem

Canonical type-`(0,n)` rational functions remain in that class after reflection.
The real exponential on the negative half-line therefore has exactly the same
attainable error bounds and infimum as the decaying exponential on the positive
half-line. Source: operator re-derivations, reciprocal exponential certificate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Polynomial Set Filter
open scoped Topology

namespace NLAlib

/-- Attainable uniform error bounds for pole-free real type-`(0,n)` rational
approximation of `exp x` on the negative half-line. -/
def negativeHalfLineExponentialUniformErrorBounds (n : ℕ) : Set ℝ :=
  {E | ∃ r : RatFunc ℝ, IsPoleFreeRationalApproximation (Iic 0) 0 n r ∧
    ∀ x : ℝ, x ≤ 0 → |Real.exp x - r.eval (RingHom.id ℝ) x| ≤ E}

/-- The actual best uniform real type-`(0,n)` rational approximation error for
`exp x` on the negative half-line. -/
def negativeHalfLineExponentialMinimaxError (n : ℕ) : ℝ :=
  sInf (negativeHalfLineExponentialUniformErrorBounds n)

private theorem isPoleFreeRationalApproximation_inv_polynomial_on {s : Set ℝ}
    (hs : 0 ∈ s) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hpole : ∀ x ∈ s, p.eval x ≠ 0) :
    IsPoleFreeRationalApproximation s 0 n ((algebraMap ℝ[X] (RatFunc ℝ) p)⁻¹) := by
  have hp0 : p ≠ 0 := by intro h; have := hpole 0 hs; simp [h] at this
  have hnum : ((algebraMap ℝ[X] (RatFunc ℝ) p)⁻¹).num ∣ (1 : ℝ[X]) := by
    simpa only [map_one, one_div] using RatFunc.num_div_dvd (1 : ℝ[X]) hp0
  have hden : ((algebraMap ℝ[X] (RatFunc ℝ) p)⁻¹).denom ∣ p := by
    simpa only [map_one, one_div] using RatFunc.denom_div_dvd (1 : ℝ[X]) p
  refine ⟨?_, (degree_le_of_dvd hden hp0).trans hp, ?_⟩
  · simpa using degree_le_of_dvd hnum (one_ne_zero : (1 : ℝ[X]) ≠ 0)
  · intro x hx hzero
    exact hpole x hx (eval_eq_zero_of_dvd_of_eval_eq_zero hden hzero)

private theorem exists_reflected_type_zero_rational {s t : Set ℝ} (ht : 0 ∈ t)
    (hreflect : ∀ x ∈ t, -x ∈ s) {n : ℕ} {r : RatFunc ℝ}
    (hr : IsPoleFreeRationalApproximation s 0 n r) :
    ∃ r' : RatFunc ℝ, IsPoleFreeRationalApproximation t 0 n r' ∧
      ∀ x ∈ t, r'.eval (RingHom.id ℝ) x = r.eval (RingHom.id ℝ) (-x) := by
  have hnum := r.num.eq_C_of_degree_le_zero hr.1
  let c : ℝ := r.num.coeff 0
  by_cases hc : c = 0
  · have hr0 : r = 0 := RatFunc.num_eq_zero_iff.mp (by
      rw [hnum]
      change C c = 0
      rw [hc, C_0])
    refine ⟨0, ?_, ?_⟩
    · refine ⟨by simp, ?_, by simp⟩
      simp only [RatFunc.denom_zero, degree_one]
      exact_mod_cast Nat.zero_le n
    · intro x _
      simp only [hr0, RatFunc.eval_zero]
  · let p : ℝ[X] := c⁻¹ • r.denom.comp (-X)
    have hp : p.degree ≤ n := by
      exact (degree_smul_le _ _).trans (by rw [degree_comp_neg_X]; exact hr.2.1)
    have hpole : ∀ x ∈ t, p.eval x ≠ 0 := by
      intro x hx
      simp only [p, eval_smul, smul_eq_mul, eval_comp, eval_neg, eval_X]
      exact mul_ne_zero (inv_ne_zero hc) (hr.2.2 (-x) (hreflect x hx))
    refine ⟨(algebraMap ℝ[X] (RatFunc ℝ) p)⁻¹,
      isPoleFreeRationalApproximation_inv_polynomial_on ht hp hpole, ?_⟩
    intro x hx
    rw [eval_inv_polynomial_of_eval_ne_zero (hpole x hx), RatFunc.eval,
      eval₂_id, eval₂_id, hnum, eval_C]
    simp only [p, eval_smul, smul_eq_mul, eval_comp, eval_neg, eval_X]
    rw [mul_inv_rev, inv_inv, div_eq_mul_inv, mul_comm]

/-- Reflection gives exact equality of the attainable native rational error
bound sets on the two half-lines, including the zero rational function.
Source: operator re-derivations, half-line reflection.
atlas: exp-rational-halfline (partial) -/
theorem negativeHalfLineExponentialUniformErrorBounds_eq (n : ℕ) :
    negativeHalfLineExponentialUniformErrorBounds n = reciprocalExponentialUniformErrorBounds n := by
  ext E
  constructor
  · rintro ⟨r, hr, herr⟩
    obtain ⟨r', hr', heval⟩ := exists_reflected_type_zero_rational
      (s := Iic 0) (t := Ici 0) (by simp)
      (by intro x hx; change (0 : ℝ) ≤ x at hx; change -x ≤ (0 : ℝ)
          exact neg_nonpos.mpr hx) hr
    refine ⟨r', hr', fun x hx => ?_⟩
    rw [heval x hx]
    exact herr (-x) (neg_nonpos.mpr hx)
  · rintro ⟨r, hr, herr⟩
    obtain ⟨r', hr', heval⟩ := exists_reflected_type_zero_rational
      (s := Ici 0) (t := Iic 0) (by simp)
      (by intro x hx; change x ≤ (0 : ℝ) at hx; change (0 : ℝ) ≤ -x
          exact neg_nonneg.mpr hx) hr
    refine ⟨r', hr', fun x hx => ?_⟩
    rw [heval x hx]
    simpa only [neg_neg] using herr (-x) (neg_nonneg.mpr hx)

/-- The actual best native rational errors on the reflected half-lines agree
exactly in every degree. Source: operator re-derivations, half-line reflection.
atlas: exp-rational-halfline (partial) -/
theorem negativeHalfLineExponentialMinimaxError_eq (n : ℕ) :
    negativeHalfLineExponentialMinimaxError n = reciprocalExponentialMinimaxError n := by
  rw [negativeHalfLineExponentialMinimaxError, reciprocalExponentialMinimaxError,
    negativeHalfLineExponentialUniformErrorBounds_eq]

/-- The actual best rational error for `exp x` on the negative half-line has the
finite geometric Laguerre lower bound. Source: reciprocal exponential certificate.
atlas: exp-rational-halfline (partial) -/
theorem negativeHalfLineExponentialMinimaxError_ge_geometric_lower_bound (n : ℕ) :
    1 / (6 * Real.sqrt (reciprocalExponentialLowerCutoff n) * 3^n) ≤
      negativeHalfLineExponentialMinimaxError n := by
  rw [negativeHalfLineExponentialMinimaxError_eq]
  exact reciprocalExponentialMinimaxError_ge_geometric_lower_bound n

/-- The explicit reciprocal construction bounds the actual best error for
`exp x` on the negative half-line in every degree. Source: focused reciprocal reroute.
atlas: exp-rational-halfline (partial) -/
theorem negativeHalfLineExponentialMinimaxError_le_geometric_upper_bound (n : ℕ) :
    negativeHalfLineExponentialMinimaxError n ≤ Real.sqrt (40 / 21) / 3^n := by
  rw [negativeHalfLineExponentialMinimaxError_eq]
  exact reciprocalExponentialMinimaxError_le_geometric_upper_bound n

/-- The actual best pole-free real type-`(0,n)` rational error for `exp x` on the
negative half-line has exact `n`th-root limit `1/3`.
Source: operator re-derivations and focused reciprocal reroute.
atlas: exp-rational-halfline (partial) -/
theorem tendsto_rpow_negativeHalfLineExponentialMinimaxError_inv_nat :
    Tendsto (fun n => (negativeHalfLineExponentialMinimaxError n) ^ (1 / (n : ℝ)))
      atTop (𝓝 (1 / 3 : ℝ)) := by
  simp_rw [negativeHalfLineExponentialMinimaxError_eq]
  exact tendsto_rpow_reciprocalExponentialMinimaxError_inv_nat

end NLAlib
