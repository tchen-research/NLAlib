import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.FieldSimp

/-! # Polynomial divided differences at a fixed scalar

Exact division by `X-z` supplies the polynomial quotient, including the
diagonal derivative value. Algebraic linearity avoids any analytic removable
singularity hypothesis.
-/

noncomputable section

namespace Polynomial

variable {𝕜 : Type*} [Field 𝕜]

/-- The polynomial `(p(X)-p(z))/(X-z)`, defined by exact monic division. -/
def dividedDifference (p : 𝕜[X]) (z : 𝕜) : 𝕜[X] :=
  (p - C (p.eval z)) /ₘ (X - C z)

/-- Multiplication by the argument difference recovers the numerator. -/
theorem X_sub_C_mul_dividedDifference (p : 𝕜[X]) (z : 𝕜) :
    (X - C z) * p.dividedDifference z = p - C (p.eval z) := by
  have hmod : (p - C (p.eval z)) %ₘ (X - C z) = 0 := by
    rw [modByMonic_X_sub_C_eq_C_eval]
    simp
  have h := modByMonic_add_div (p - C (p.eval z)) (X - C z)
  rw [hmod, zero_add] at h
  exact h

/-- Constants have zero divided difference. -/
@[simp] theorem dividedDifference_C (a z : 𝕜) : (C a).dividedDifference z = 0 := by
  apply mul_left_cancel₀ (monic_X_sub_C z).ne_zero
  rw [X_sub_C_mul_dividedDifference]
  simp

/-- Divided differences preserve polynomial addition. -/
@[simp] theorem dividedDifference_add (p q : 𝕜[X]) (z : 𝕜) :
    (p + q).dividedDifference z = p.dividedDifference z + q.dividedDifference z := by
  apply mul_left_cancel₀ (monic_X_sub_C z).ne_zero
  rw [mul_add, X_sub_C_mul_dividedDifference, X_sub_C_mul_dividedDifference,
    X_sub_C_mul_dividedDifference, eval_add, map_add]
  ring

/-- Divided differences preserve multiplication by scalar constants. -/
@[simp] theorem dividedDifference_C_mul (a : 𝕜) (p : 𝕜[X]) (z : 𝕜) :
    (C a * p).dividedDifference z = C a * p.dividedDifference z := by
  apply mul_left_cancel₀ (monic_X_sub_C z).ne_zero
  rw [X_sub_C_mul_dividedDifference, mul_left_comm, X_sub_C_mul_dividedDifference,
    eval_mul, eval_C, map_mul]
  ring

/-- Divided differences preserve polynomial subtraction. -/
@[simp] theorem dividedDifference_sub (p q : 𝕜[X]) (z : 𝕜) :
    (p - q).dividedDifference z = p.dividedDifference z - q.dividedDifference z := by
  apply mul_left_cancel₀ (monic_X_sub_C z).ne_zero
  rw [mul_sub, X_sub_C_mul_dividedDifference, X_sub_C_mul_dividedDifference,
    X_sub_C_mul_dividedDifference, eval_sub, map_sub]
  ring

/-- The product by `X` contributes its evaluation as a constant term. -/
theorem dividedDifference_X_mul (p : 𝕜[X]) (z : 𝕜) :
    (X * p).dividedDifference z = X * p.dividedDifference z + C (p.eval z) := by
  apply mul_left_cancel₀ (monic_X_sub_C z).ne_zero
  rw [X_sub_C_mul_dividedDifference, mul_add, mul_left_comm,
    X_sub_C_mul_dividedDifference, eval_mul, eval_X, map_mul]
  ring

/-- The divided difference of the constant one is zero. -/
@[simp] theorem dividedDifference_one (z : 𝕜) : (1 : 𝕜[X]).dividedDifference z = 0 := by
  simpa only [C_1] using dividedDifference_C (1 : 𝕜) z

/-- The divided difference of `X` is one. -/
@[simp] theorem dividedDifference_X (z : 𝕜) : (X : 𝕜[X]).dividedDifference z = 1 := by
  simpa only [mul_one, dividedDifference_one, mul_zero, zero_add, eval_one, C_1] using
    dividedDifference_X_mul (1 : 𝕜[X]) z

/-- A positive degree bound drops by at least one under divided differences. -/
theorem degree_dividedDifference_lt {p : 𝕜[X]} {n : ℕ} (hn : 0 < n)
    (hp : p.natDegree ≤ n) (z : 𝕜) : (p.dividedDifference z).degree < n := by
  by_cases hq : p.dividedDifference z = 0
  · rw [hq, degree_zero]
    exact WithBot.bot_lt_coe _
  apply (natDegree_lt_iff_degree_lt hq).mp
  have hnum : (p - C (p.eval z)).natDegree ≤ n :=
    (natDegree_sub_le _ _).trans (max_le hp (by rw [natDegree_C]; exact Nat.zero_le n))
  rw [dividedDifference, natDegree_divByMonic _ (monic_X_sub_C z), natDegree_X_sub_C]
  omega

/-- The diagonal quotient value is the ordinary polynomial derivative. -/
theorem eval_dividedDifference_self (p : 𝕜[X]) (z : 𝕜) :
    (p.dividedDifference z).eval z = p.derivative.eval z := by
  have h := congrArg (fun q : 𝕜[X] => q.derivative.eval z)
    (X_sub_C_mul_dividedDifference p z)
  simpa only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C,
    sub_self, zero_mul, add_zero] using h

/-- Exact evaluation of the quotient at distinct arguments. -/
theorem eval_dividedDifference_of_ne (p : 𝕜[X]) {x z : 𝕜} (hx : x ≠ z) :
    (p.dividedDifference z).eval x = (p.eval x - p.eval z) / (x - z) := by
  apply (eq_div_iff (sub_ne_zero.mpr hx)).mpr
  have h := congrArg (eval x) (X_sub_C_mul_dividedDifference p z)
  simpa only [eval_mul, eval_sub, eval_X, eval_C, mul_comm] using h

/-- The polynomial divided difference is symmetric in its two evaluations,
including equal arguments. -/
theorem eval_dividedDifference_comm (p : 𝕜[X]) (x y : 𝕜) :
    (p.dividedDifference x).eval y = (p.dividedDifference y).eval x := by
  by_cases hxy : x = y
  · subst y
    rfl
  rw [eval_dividedDifference_of_ne p (fun h => hxy h.symm), eval_dividedDifference_of_ne p hxy]
  field_simp
  ring

end Polynomial
