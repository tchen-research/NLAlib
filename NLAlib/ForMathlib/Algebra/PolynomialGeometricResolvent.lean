import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp

/-! # Finite polynomial expansions of a scalar resolvent

The finite geometric resolvent expansion and its exact remainder are algebraic
identities over a field, including the empty expansion.
-/

noncomputable section
open Polynomial Finset
namespace Polynomial
variable {𝕜 : Type*} [Field 𝕜]

/-- The first `m` monomial terms in the expansion of `1/(z-X)` at infinity.
The definition is total, including `z=0` and `m=0`. -/
def geometricResolventPolynomial (z : 𝕜) (m : ℕ) : 𝕜[X] :=
  ∑ j : Fin m, C (z⁻¹ ^ (j.val + 1)) * X ^ j.val

/-- The finite resolvent expansion has degree strictly below its length,
including the zero polynomial at length zero. -/
theorem degree_geometricResolventPolynomial_lt (z : 𝕜) (m : ℕ) :
    (geometricResolventPolynomial z m).degree < m :=
  degree_sum_fin_lt _

/-- Appending one term to the finite expansion appends its displayed monomial. -/
theorem geometricResolventPolynomial_succ (z : 𝕜) (m : ℕ) :
    geometricResolventPolynomial z (m+1) = geometricResolventPolynomial z m +
      C (z⁻¹ ^ (m+1)) * X ^ m := by
  simp only [geometricResolventPolynomial, Fin.sum_univ_castSucc,
    Fin.val_castSucc, Fin.val_last]

/-- The exact finite resolvent remainder is `t^m/(z^m*(z-t))`.
No infinite series or convergence hypothesis is used. -/
theorem inv_sub_eval_geometricResolventPolynomial_eq {z t : 𝕜}
    (hz : z ≠ 0) (hzt : z ≠ t) (m : ℕ) :
    (z-t)⁻¹ - (geometricResolventPolynomial z m).eval t = t^m/(z^m*(z-t)) := by
  induction m with
  | zero => simp [geometricResolventPolynomial, one_div]
  | succ m ih =>
    rw [geometricResolventPolynomial_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X,
      ← sub_sub, ih]
    rw [inv_pow]
    field_simp [hz, sub_ne_zero.mpr hzt]
    ring

end Polynomial
