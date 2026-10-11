import NLAlib.Polynomial.SawtoothInterpolation
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Polynomial derivative and zero counting for sawtooth interpolation

The odd sine interpolant has derivative polynomial in `cos(t)` of degree at most `n`.
Its sawtooth error derivative is the negative of a nonzero degree-`n` polynomial.
These are the exact finite zero-count prerequisites for sharp Jackson's constant.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real

namespace NLAlib

/-- The derivative polynomial of the explicit odd trigonometric sawtooth interpolant.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
def sawtoothDerivativePolynomial (n : ℕ) : ℝ[X] :=
  X * sawtoothSineInterp n - (1 - X ^ 2) * (sawtoothSineInterp n).derivative

/-- The polynomial controlling the negative sawtooth-error derivative.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
def sawtoothErrorDerivativePolynomial (n : ℕ) : ℝ[X] := 1 + sawtoothDerivativePolynomial n

/-- The odd sawtooth approximant has its explicit derivative polynomial at every real angle.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
theorem hasDerivAt_sawtoothApprox (n : ℕ) (t : ℝ) :
    HasDerivAt (sawtoothApprox n) ((sawtoothDerivativePolynomial n).eval (cos t)) t := by
  have h := (hasDerivAt_sin t).mul
    (((sawtoothSineInterp n).hasDerivAt (cos t)).comp t (hasDerivAt_cos t))
  convert h using 1 <;> try rfl
  simp only [sawtoothDerivativePolynomial, eval_sub, eval_mul, eval_X, eval_one, eval_pow,
    Function.comp_apply]
  linear_combination (sawtoothSineInterp n).derivative.eval (cos t) * sin_sq_add_cos_sq t

/-- The error `pi-t-τ_n(t)` has the negative of the nonzero polynomial derivative.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
theorem hasDerivAt_sawtoothError (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.pi - t - sawtoothApprox n t)
      (-(sawtoothErrorDerivativePolynomial n).eval (cos t)) t := by
  have h := ((hasDerivAt_const t Real.pi).sub (hasDerivAt_id t)).sub
    (hasDerivAt_sawtoothApprox n t)
  convert h using 1 <;> try rfl
  simp [sawtoothErrorDerivativePolynomial]
  ring

/-- The derivative polynomial has degree at most the trigonometric cutoff.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
theorem degree_sawtoothDerivativePolynomial_le (n : ℕ) :
    (sawtoothDerivativePolynomial n).degree ≤ n := by
  apply degree_le_of_natDegree_le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sawtoothDerivativePolynomial, sawtoothSineInterp]
  · let p := sawtoothSineInterp n
    have hp : p.natDegree < n := by
      rcases eq_or_ne p 0 with hp0 | hp0
      · simpa [hp0] using hn
      · exact (natDegree_lt_iff_degree_lt hp0).mpr (degree_sawtoothSineInterp_lt n)
    change (X * p - (1 - X ^ 2) * p.derivative).natDegree ≤ n
    have hX : (X * p : ℝ[X]).natDegree ≤ 1 + p.natDegree := by
      simpa only [natDegree_X] using (natDegree_mul_le (p := (X : ℝ[X])) (q := p))
    rcases Nat.eq_zero_or_pos p.natDegree with hp0 | hp0
    · rw [Polynomial.derivative_eq_zero.mpr hp0, mul_zero, sub_zero]
      omega
    · have hquadratic : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 := by
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_) <;> simp
      have hD : ((1 - X ^ 2) * p.derivative : ℝ[X]).natDegree ≤ 2 + (p.natDegree - 1) :=
        (natDegree_mul_le (p := 1 - X ^ 2) (q := p.derivative)).trans
          (Nat.add_le_add hquadratic (natDegree_derivative_le p))
      exact (natDegree_sub_le _ _).trans (max_le (by omega) (by omega))

/-- The polynomial controlling error zeros has degree at most `n`.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
theorem degree_sawtoothErrorDerivativePolynomial_le (n : ℕ) :
    (sawtoothErrorDerivativePolynomial n).degree ≤ n := by
  unfold sawtoothErrorDerivativePolynomial
  refine (degree_add_le _ _).trans (max_le ?_ (degree_sawtoothDerivativePolynomial_le n))
  exact degree_one_le.trans (by exact_mod_cast Nat.zero_le n)

/-- The sawtooth-error derivative polynomial is nonzero: Rolle's theorem on the odd
approximant itself provides a point where its derivative is zero, hence this polynomial
takes value one. No mean or zero-count premise is assumed.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
theorem sawtoothErrorDerivativePolynomial_ne_zero (n : ℕ) :
    sawtoothErrorDerivativePolynomial n ≠ 0 := by
  have hc : Continuous (sawtoothApprox n) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_sawtoothApprox n t).continuousAt)
  obtain ⟨t, ht, hd⟩ := exists_hasDerivAt_eq_zero Real.pi_pos hc.continuousOn
    (by simp) (fun t _ => hasDerivAt_sawtoothApprox n t)
  intro hzero
  have h := congrArg (Polynomial.eval (cos t)) hzero
  simp only [sawtoothErrorDerivativePolynomial, eval_add, eval_one, eval_zero, hd] at h
  norm_num at h

end NLAlib
