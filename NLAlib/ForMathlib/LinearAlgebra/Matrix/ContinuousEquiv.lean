import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuous equivalence from a nonsingular finite matrix

An invertible matrix acts as a continuous linear equivalence on its coordinate
space. This bridges the actual peak-difference determinant to the inverse
function theorem.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

/-- A real finite square matrix of nonzero determinant induces a continuous
linear equivalence with exactly its matrix-vector action.
Source: finite-dimensional linear algebra; universal Lebesgue comparison helper. -/
theorem exists_continuousLinearEquiv_apply_eq_mulVec {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    ∃ e : (ι → ℝ) ≃L[ℝ] (ι → ℝ), ∀ x, e x = A *ᵥ x := by
  refine ⟨(A.toLinearEquiv (Pi.basisFun ℝ ι) (isUnit_iff_ne_zero.mpr hA)).toContinuousLinearEquiv, ?_⟩
  intro x
  rfl

end NLAlib
