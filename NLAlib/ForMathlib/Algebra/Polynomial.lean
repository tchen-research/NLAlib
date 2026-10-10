import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Real.Basic

/-!
# Elementary facts about real polynomials

General facts not about NLAlib's objects; candidates for upstreaming to
`Mathlib/Algebra/Polynomial/`.

* `degree_C_mul_le`: multiplying by a constant does not raise the degree;
* `eq_zero_of_forall_abs_eval_le_of_nonpos`: a polynomial bounded by `M ≤ 0` on `[−1, 1]` is `0`;
* `eval_iterate_derivative_natDegree`: the `n`-th derivative of a degree-`n` polynomial is the
  constant `n! · leadingCoeff`.

Used by `NLAlib.Polynomial.Minimax` and `NLAlib.Polynomial.Interpolation`.
-/

namespace NLAlib

open Polynomial

/-- Multiplying by a constant does not raise the degree. (Mathlib has `natDegree_C_mul_le`.) -/
theorem degree_C_mul_le {R : Type*} [Semiring R] (c : R) (P : R[X]) :
    (C c * P).degree ≤ P.degree := by
  rw [C_mul']
  exact degree_smul_le _ _

/-- A real polynomial bounded by `M ≤ 0` on `[−1, 1]` is zero. -/
theorem eq_zero_of_forall_abs_eval_le_of_nonpos {P : ℝ[X]} {M : ℝ} (hM : M ≤ 0)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ M) : P = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono (fun x hx => ?_) (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1))
  have := hP x hx
  have h0 : |P.eval x| = 0 := le_antisymm (this.trans hM) (abs_nonneg _)
  exact abs_eq_zero.mp h0

/-- The `n`-th derivative of a polynomial of degree `n` is the constant `n! · leadingCoeff`. -/
theorem eval_iterate_derivative_natDegree (p : ℝ[X]) (x : ℝ) :
    (derivative^[p.natDegree] p).eval x = p.natDegree.factorial * p.leadingCoeff := by
  have h : (derivative^[p.natDegree] p).natDegree ≤ 0 :=
    (natDegree_iterate_derivative p _).trans (by omega)
  rw [eq_C_of_natDegree_le_zero h, eval_C, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul, leadingCoeff]

end NLAlib
