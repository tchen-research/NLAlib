import NLAlib.Polynomial.BestApproximation.ReciprocalExponentialUpper
import NLAlib.Polynomial.BestApproximation.ExponentialReciprocalLower
import NLAlib.Polynomial.BestApproximation.Basic

/-!
# Actual type-`(0,n)` rational minimax bounds on the half-line

The infimum is over Mathlib's canonical rational functions with the library's
native degree and pole-free predicates. Constant numerators are normalized to
reciprocal polynomials before applying the finite Laguerre lower certificate.
Source: focused reciprocal reroute, Section 1 and retained lower-bound appendix.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Set
namespace NLAlib

/-- Attainable uniform-error bounds for type-`(0,n)` pole-free real rational
approximation of the decaying exponential on the entire positive half-line. -/
def reciprocalExponentialUniformErrorBounds (n : ℕ) : Set ℝ :=
  {E | ∃ r : RatFunc ℝ, IsPoleFreeRationalApproximation (Ici 0) 0 n r ∧
    ∀ x : ℝ, 0 ≤ x → |Real.exp (-x)-r.eval (RingHom.id ℝ) x| ≤ E}

/-- The actual best uniform type-`(0,n)` rational error on the positive half-line.
The infimum uses attainable uniform bounds, so no bounded-continuous-map
instance or unproved minimizer is required on the noncompact domain. -/
def reciprocalExponentialMinimaxError (n : ℕ) : ℝ :=
  sInf (reciprocalExponentialUniformErrorBounds n)

/-- A reciprocal polynomial has the allowed native rational degree budgets and
inherits the polynomial's pole-free domain, even after canonical reduction. -/
theorem isPoleFreeRationalApproximation_inv_polynomial {n : ℕ} {p : ℝ[X]}
    (hp : p.degree ≤ n) (hpole : ∀ x : ℝ, 0 ≤ x → p.eval x ≠ 0) :
    IsPoleFreeRationalApproximation (Ici 0) 0 n
      ((algebraMap ℝ[X] (RatFunc ℝ) p)⁻¹) := by
  have hp0 : p ≠ 0 := by intro h; have := hpole 0 le_rfl; simp [h] at this
  have hnum : ((algebraMap ℝ[X] (RatFunc ℝ) p)⁻¹).num ∣ (1:ℝ[X]) := by
    simpa only [map_one, one_div] using RatFunc.num_div_dvd (1:ℝ[X]) hp0
  have hden : ((algebraMap ℝ[X] (RatFunc ℝ) p)⁻¹).denom ∣ p := by
    simpa only [map_one, one_div] using RatFunc.denom_div_dvd (1:ℝ[X]) p
  refine ⟨?_, (degree_le_of_dvd hden hp0).trans hp, ?_⟩
  · simpa using degree_le_of_dvd hnum (one_ne_zero : (1:ℝ[X]) ≠ 0)
  · intro x hx hzero
    exact hpole x hx (eval_eq_zero_of_dvd_of_eval_eq_zero hden hzero)

/-- Canonical rational evaluation of a pole-free reciprocal polynomial agrees
with the reciprocal of its polynomial evaluation. -/
theorem eval_inv_polynomial_of_eval_ne_zero {p : ℝ[X]} {x : ℝ} (hp : p.eval x ≠ 0) :
    ((algebraMap ℝ[X] (RatFunc ℝ) p)⁻¹).eval (RingHom.id ℝ) x = (p.eval x)⁻¹ := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  let r : RatFunc ℝ := (algebraMap ℝ[X] (RatFunc ℝ) p)⁻¹
  have hden : r.denom.eval x ≠ 0 := by
    have hdvd : r.denom ∣ p := by
      simpa only [r, map_one, one_div] using RatFunc.denom_div_dvd (1:ℝ[X]) p
    exact fun h => hp (eval_eq_zero_of_dvd_of_eval_eq_zero hdvd h)
  have hcross : r.num*p = r.denom := by
    have h := (RatFunc.num_mul_eq_mul_denom_iff hp0).mpr
      (show r = algebraMap ℝ[X] (RatFunc ℝ) (1:ℝ[X]) /
        algebraMap ℝ[X] (RatFunc ℝ) p by simp [r])
    simpa only [one_mul] using h
  have hv := congrArg (Polynomial.eval x) hcross
  rw [eval_mul] at hv
  change r.eval (RingHom.id ℝ) x = _
  rw [RatFunc.eval, eval₂_id, eval₂_id]
  field_simp
  exact hv

/-- Every actual pole-free type-`(0,n)` rational function satisfies the geometric
lower certificate, including the zero-numerator branch.
Source: retained reciprocal lower-bound appendix.
atlas: exp-rational-halfline (partial) -/
theorem type_zero_rational_exp_error_ge_geometric_lower_bound
    {n : ℕ} {r : RatFunc ℝ} (hr : IsPoleFreeRationalApproximation (Ici 0) 0 n r)
    {E : ℝ} (herr : ∀ x : ℝ, 0 ≤ x → |Real.exp (-x)-r.eval (RingHom.id ℝ) x| ≤ E) :
    1/(6*Real.sqrt (reciprocalExponentialLowerCutoff n)*3^n) ≤ E := by
  have hnum := r.num.eq_C_of_degree_le_zero hr.1
  let c : ℝ := r.num.coeff 0
  by_cases hc : c=0
  · have hr0 : r=0 := RatFunc.num_eq_zero_iff.mp (by
      rw [hnum]
      change C c = 0
      rw [hc, C_0])
    have hE : 1 ≤ E := by simpa [hr0] using herr 0 le_rfl
    have hbound := reciprocal_exp_neg_error_ge_geometric_lower_bound
      (p := C 1) (degree_C_le.trans (by exact_mod_cast Nat.zero_le n))
      (E := 1) (by simp) (by
        intro x hx
        have he : Real.exp (-x) ≤ 1 := by
          simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
        simp only [eval_C, inv_one]
        exact abs_le.mpr ⟨by have := Real.exp_pos (-x); linarith, by linarith⟩)
    exact hbound.trans hE
  · let p : ℝ[X] := c⁻¹ • r.denom
    have hp : p.degree ≤ n := (degree_smul_le _ _).trans hr.2.1
    have hpole : ∀ x : ℝ, 0 ≤ x → p.eval x ≠ 0 := by
      intro x hx
      simp only [p, eval_smul, smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero hc) (hr.2.2 x hx)
    have heval (x : ℝ) : r.eval (RingHom.id ℝ) x = (p.eval x)⁻¹ := by
      rw [RatFunc.eval, eval₂_id, eval₂_id, hnum, eval_C]
      simp only [p, eval_smul, smul_eq_mul]
      change c/r.denom.eval x = (c⁻¹*r.denom.eval x)⁻¹
      rw [mul_inv_rev, inv_inv, div_eq_mul_inv, mul_comm]
    apply reciprocal_exp_neg_error_ge_geometric_lower_bound hp hpole
    intro x hx
    simpa only [← heval x] using herr x hx

/-- The error-bound set is nonempty in every degree. The zero rational function
has uniform exponential error at most one. -/
theorem reciprocalExponentialUniformErrorBounds_nonempty (n : ℕ) :
    (reciprocalExponentialUniformErrorBounds n).Nonempty := by
  refine ⟨1, 0, ?_, ?_⟩
  · refine ⟨by simp, ?_, by simp⟩
    simp only [RatFunc.denom_zero, degree_one]
    exact_mod_cast Nat.zero_le n
  · intro x hx
    simp only [RatFunc.eval_zero, sub_zero, abs_of_pos (Real.exp_pos _)]
    simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hx)

/-- Every attainable uniform error is nonnegative, so its infimum is finite. -/
theorem reciprocalExponentialUniformErrorBounds_bddBelow (n : ℕ) :
    BddBelow (reciprocalExponentialUniformErrorBounds n) := by
  refine ⟨0, ?_⟩
  rintro E ⟨r, _, herr⟩
  exact (abs_nonneg _).trans (herr 0 le_rfl)

/-- The actual rational minimax error has the finite Laguerre geometric lower
bound. No minimizer or polynomial certificate is assumed.
Source: focused reciprocal reroute and retained lower-bound appendix.
atlas: exp-rational-halfline (partial) -/
theorem reciprocalExponentialMinimaxError_ge_geometric_lower_bound (n : ℕ) :
    1/(6*Real.sqrt (reciprocalExponentialLowerCutoff n)*3^n) ≤
      reciprocalExponentialMinimaxError n := by
  apply le_csInf (reciprocalExponentialUniformErrorBounds_nonempty n)
  rintro E ⟨r, hr, herr⟩
  exact type_zero_rational_exp_error_ge_geometric_lower_bound hr herr

/-- The explicit denominator bounds the actual rational minimax error in every
degree, with the sharper constant `√(40/21)` from the focused reroute.
atlas: exp-rational-halfline (partial) -/
theorem reciprocalExponentialMinimaxError_le_geometric_upper_bound (n : ℕ) :
    reciprocalExponentialMinimaxError n ≤ Real.sqrt (40/21)/3^n := by
  apply csInf_le (reciprocalExponentialUniformErrorBounds_bddBelow n)
  refine ⟨(algebraMap ℝ[X] (RatFunc ℝ) (reciprocalExponentialDenominator n))⁻¹, ?_, ?_⟩
  · apply isPoleFreeRationalApproximation_inv_polynomial
    · exact degree_le_of_natDegree_le (by rw [natDegree_reciprocalExponentialDenominator])
    · exact fun x hx => (reciprocalExponentialDenominator_eval_pos n hx).ne'
  · intro x hx
    rw [eval_inv_polynomial_of_eval_ne_zero
      (reciprocalExponentialDenominator_eval_pos n hx).ne']
    exact abs_exp_neg_sub_inv_reciprocalExponentialDenominator_le n hx

end NLAlib
