import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

/-! # Odd polynomial updates in coefficient coordinates

The coefficient representation supplies every odd polynomial of degree at
most `2q+1`. It is shared by scalar minimax analysis and matrix realizations.
Source: Polar Express, §2, equations (3)–(6).
-/
noncomputable section
open Finset Polynomial
namespace NLAlib

/-- An odd degree-at-most-`2q+1` update, in its supplied scalar coefficients. -/
def oddScalarUpdate (q : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (q + 1), a j * x ^ (2 * j + 1)

/-- The corresponding ordinary real polynomial. -/
def oddUpdatePolynomial (q : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ range (q + 1), C (a j) * X ^ (2 * j + 1)

/-- The coefficient-defined scalar update is the evaluation of its polynomial. -/
theorem eval_oddUpdatePolynomial (q : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    (oddUpdatePolynomial q a).eval x = oddScalarUpdate q a x := by
  simp [oddUpdatePolynomial, oddScalarUpdate, Polynomial.eval_finsetSum]

/-- The scalar update is continuous everywhere. -/
theorem continuous_oddScalarUpdate (q : ℕ) (a : ℕ → ℝ) : Continuous (oddScalarUpdate q a) := by
  unfold oddScalarUpdate
  fun_prop

/-- Odd updates annihilate a zero singular direction. -/
@[simp] theorem oddScalarUpdate_zero (q : ℕ) (a : ℕ → ℝ) : oddScalarUpdate q a 0 = 0 := by
  simp [oddScalarUpdate]

/-- Oddness is a proved property of the actual coefficient expression. -/
theorem oddScalarUpdate_neg (q : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    oddScalarUpdate q a (-x) = -oddScalarUpdate q a x := by
  simp [oddScalarUpdate, pow_add, pow_mul, Finset.sum_neg_distrib]

/-- Apply the successive coefficient-defined updates, starting from the input. -/
def oddScalarComposition (q : ℕ) (a : ℕ → ℕ → ℝ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | k + 1 => oddScalarUpdate q (a k) (oddScalarComposition q a x k)

/-- Every finite composition is continuous. -/
theorem continuous_oddScalarComposition (q : ℕ) (a : ℕ → ℕ → ℝ) (k : ℕ) :
    Continuous (fun x => oddScalarComposition q a x k) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih => exact (continuous_oddScalarUpdate q (a k)).comp ih

/-- Every finite composition fixes a zero singular direction at zero. -/
@[simp] theorem oddScalarComposition_zero (q : ℕ) (a : ℕ → ℕ → ℝ) (k : ℕ) :
    oddScalarComposition q a 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [oddScalarComposition, ih]

end NLAlib
