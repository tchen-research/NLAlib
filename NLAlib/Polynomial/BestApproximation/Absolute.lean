import NLAlib.Polynomial.BestApproximation.MinimaxError
import NLAlib.Polynomial.FunctionApproximation.AbsoluteChebyshevSeries

/-!
# Best polynomial approximation of absolute value

The native uniform approximation error on the real unit interval has finite
minimizers and the explicit even-degree Chebyshev comparison bound.
Source: the focused polynomial Bernstein reroute, Section 2.
-/

noncomputable section

open Polynomial Set

namespace NLAlib

/-- Absolute value as a continuous function on the real unit interval. -/
def absoluteValueOnUnitInterval : C(Icc (-1 : ℝ) 1, ℝ) :=
  ⟨fun x => |(x : ℝ)|, continuous_abs.comp continuous_subtype_val⟩

/-- The best uniform error for approximating absolute value by real polynomials
of degree at most `n` on the unit interval. -/
def absoluteMinimaxError (n : ℕ) : ℝ := minimaxError n absoluteValueOnUnitInterval

/-- The best absolute-value approximation error is nonnegative. -/
theorem absoluteMinimaxError_nonneg (n : ℕ) : 0 ≤ absoluteMinimaxError n :=
  minimaxError_nonneg n absoluteValueOnUnitInterval

/-- The best absolute-value approximation error decreases with degree. -/
theorem absoluteMinimaxError_antitone : Antitone absoluteMinimaxError :=
  minimaxError_antitone absoluteValueOnUnitInterval

/-- An actual degree-bounded polynomial attains the absolute-value approximation
error, and thus supplies its pointwise uniform bound. -/
theorem exists_degree_le_absoluteMinimaxError (n : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      |(|x|) - p.eval x| ≤ absoluteMinimaxError n := by
  obtain ⟨p, hp, heq⟩ := exists_degree_le_norm_sub_eq_minimaxError n
    absoluteValueOnUnitInterval
  refine ⟨p, hp, fun x hx => ?_⟩
  exact ((absoluteValueOnUnitInterval - p.toContinuousMapOn (Icc (-1 : ℝ) 1)).norm_coe_le_norm
    ⟨x, hx⟩).trans_eq heq

/-- Every degree-bounded real polynomial competitor gives an upper bound for
the best absolute-value approximation error. -/
theorem absoluteMinimaxError_le_of_degree_le {n : ℕ} {p : ℝ[X]} {E : ℝ}
    (hp : p.degree ≤ n) (hE : ∀ x ∈ Icc (-1 : ℝ) 1, |(|x|) - p.eval x| ≤ E) :
    absoluteMinimaxError n ≤ E := by
  exact (isLeast_minimaxError_pointwise (by norm_num : (-1 : ℝ) ≤ 1) n
    absoluteValueOnUnitInterval).2 ⟨p, hp, fun x => hE x x.property⟩

/-- The exact absolute Chebyshev tail gives the degree-`2m` comparison bound. -/
theorem absoluteMinimaxError_even_le (m : ℕ) :
    absoluteMinimaxError (2 * m) ≤ 2 / (Real.pi * (2 * m + 1)) := by
  exact absoluteMinimaxError_le_of_degree_le
    (degree_chebyshevTrunc_le _ _) (fun _ hx => abs_abs_sub_eval_chebyshevTrunc_le m hx)

private theorem coeff_comp_neg_X (p : ℝ[X]) (k : ℕ) :
    (p.comp (-X)).coeff k = (-1:ℝ)^k * p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq]; ring
  | monomial j c =>
    rw [monomial_comp, neg_pow, ← mul_assoc,
      show (-1:ℝ[X])^j = C ((-1:ℝ)^j) by simp, ← C_mul,
      C_mul_X_pow_eq_monomial]
    simp only [coeff_monomial]
    split_ifs with h
    · subst j
      ring
    · simp

/-- Odd degree gives no improvement over the preceding even degree for the
best uniform approximation of absolute value. Symmetrization cancels its leading
odd coefficient and cannot increase the error.
Source: focused polynomial Bernstein reroute, finite parity reduction.
atlas: abs-best-approx-asymptotics (partial) -/
theorem absoluteMinimaxError_odd_eq_even (m : ℕ) :
    absoluteMinimaxError (2*m+1) = absoluteMinimaxError (2*m) := by
  apply le_antisymm (absoluteMinimaxError_antitone (by omega))
  obtain ⟨p, hp, he⟩ := exists_degree_le_absoluteMinimaxError (2*m+1)
  let q := (1/2:ℝ) • (p+p.comp (-X))
  have hqbound : q.degree ≤ (2*m+1:ℕ) :=
    (degree_smul_le _ _).trans (degree_add_le_of_degree_le hp (by simpa using hp))
  have hq : q.degree ≤ (2*m:ℕ) := by
    apply (degree_le_iff_coeff_zero _ _).mpr
    intro k hk
    have hkNat : 2*m < k := by exact_mod_cast hk
    by_cases hkEq : k = 2*m+1
    · subst k
      simp only [q, coeff_smul, smul_eq_mul, coeff_add, coeff_comp_neg_X,
        pow_add, pow_mul]
      norm_num
    · exact coeff_eq_zero_of_degree_lt (hqbound.trans_lt (by exact_mod_cast (show 2*m+1<k by omega)))
  apply absoluteMinimaxError_le_of_degree_le hq
  intro x hx
  have hneg : -x ∈ Icc (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hsum := (abs_add_le (|x|-p.eval x) (|x|-p.eval (-x))).trans
    (add_le_add (he x hx) (by simpa only [abs_neg] using he (-x) hneg))
  have heval : |x|-q.eval x = (1/2:ℝ)*((|x|-p.eval x)+(|x|-p.eval (-x))) := by
    simp only [q, eval_smul, smul_eq_mul, eval_add, eval_comp, eval_neg, eval_X]
    ring
  rw [heval, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  linarith

end NLAlib
