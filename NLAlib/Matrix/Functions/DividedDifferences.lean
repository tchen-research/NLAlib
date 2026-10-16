import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Symmetric
import NLAlib.ForMathlib.Algebra.PolynomialDividedDifference

/-!
# Löwner matrices and confluent divided differences

Mathlib's `dslope` already is the first divided difference with the actual
derivative at repeated nodes. The Löwner matrix uses this object directly,
including repeated nodes and Mathlib's total derivative convention.
Tropp (2022), Definitions 14.3–14.4. Atlas: `matrix-divided-differences-def`.
-/

noncomputable section

namespace NLAlib

/-- The Löwner matrix on a finite family of real nodes, using Mathlib's
confluent divided difference. Tropp (2022), Definitions 14.3–14.4.
atlas: matrix-divided-differences-def -/
def loewnerMatrix {ι : Type*} (f : ℝ → ℝ) (nodes : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => dslope f (nodes i) (nodes j)

/-- Repeated nodes use the derivative, rather than division by zero. -/
@[simp] theorem loewnerMatrix_apply_self {ι : Type*} (f : ℝ → ℝ)
    (nodes : ι → ℝ) (i : ι) : loewnerMatrix f nodes i i = deriv f (nodes i) :=
  dslope_same _ _

/-- At unequal nodes the Löwner matrix is the usual scalar difference quotient. -/
theorem loewnerMatrix_apply_of_ne {ι : Type*} (f : ℝ → ℝ) (nodes : ι → ℝ)
    (i j : ι) (h : nodes i ≠ nodes j) :
    loewnerMatrix f nodes i j = (f (nodes i) - f (nodes j)) / (nodes i - nodes j) := by
  rw [loewnerMatrix, dslope_of_ne f (Ne.symm h)]
  simp only [slope, vsub_eq_sub, smul_eq_mul]
  field_simp
  ring

/-- The confluent scalar divided difference is symmetric, without a
differentiability hypothesis away from its total diagonal value. -/
theorem dslope_swap (f : ℝ → ℝ) (x y : ℝ) : dslope f x y = dslope f y x := by
  by_cases h : x = y
  · subst y; rfl
  rw [dslope_of_ne f (Ne.symm h), dslope_of_ne f h]
  simp only [slope, vsub_eq_sub, smul_eq_mul]
  field_simp
  ring

/-- Every Löwner matrix is symmetric, including confluent node families. -/
theorem loewnerMatrix_isSymm {ι : Type*} (f : ℝ → ℝ) (nodes : ι → ℝ) :
    (loewnerMatrix f nodes).IsSymm := by
  ext i j
  exact dslope_swap f _ _

/-- Polynomial Löwner entries agree with evaluation of the existing exact
polynomial divided difference, including the confluent derivative value. -/
theorem dslope_polynomial_eq_eval_dividedDifference (p : Polynomial ℝ) (x y : ℝ) :
    dslope (fun t => p.eval t) x y = (p.dividedDifference x).eval y := by
  by_cases h : y = x
  · subst y
    rw [dslope_same, Polynomial.eval_dividedDifference_self]
    exact p.deriv
  rw [dslope_of_ne _ h, Polynomial.eval_dividedDifference_of_ne p h]
  simp only [slope, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul]

end NLAlib
