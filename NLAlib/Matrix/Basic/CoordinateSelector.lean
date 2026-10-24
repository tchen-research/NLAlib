import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Mul

/-! # Coordinate projections and padded row restriction

The same diagonal selector represents a coordinate projection and selects
rows while retaining the ambient labels. This is the existing Schur–Horn
selector, moved to the matrix basics and generalized to both scalar fields.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [DecidableEq n]

/-- The diagonal projection onto a finite set of coordinate labels. -/
def coordinateSelector (S : Finset n) : Matrix n n 𝕜 :=
  Matrix.diagonal (fun i => if i ∈ S then 1 else 0)

/-- A coordinate selector is Hermitian over either scalar field. -/
theorem coordinateSelector_isHermitian (S : Finset n) :
    (coordinateSelector S : Matrix n n 𝕜).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  change star (fun i => if i ∈ S then (1 : 𝕜) else 0) = _
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

variable [Fintype n]

/-- Multiplication by a coordinate selector retains the selected rows and
sets all other rows to zero. -/
theorem coordinateSelector_mul_apply (S : Finset n) (X : Matrix n d 𝕜) (i : n) (j : d) :
    ((coordinateSelector S : Matrix n n 𝕜) * X) i j = if i ∈ S then X i j else 0 := by
  rw [coordinateSelector, Matrix.diagonal_mul]
  split_ifs <;> simp

/-- Coordinate restriction is an idempotent projection. -/
theorem coordinateSelector_mul_self (S : Finset n) :
    (coordinateSelector S : Matrix n n 𝕜) * coordinateSelector S = coordinateSelector S := by
  ext i j
  rw [coordinateSelector_mul_apply]
  by_cases hi : i ∈ S
  · simp [hi]
  · by_cases hij : i = j
    · subst j; simp [coordinateSelector, hi]
    · simp [coordinateSelector, hij]

/-- Selecting every coordinate leaves a matrix unchanged. -/
@[simp] theorem coordinateSelector_univ :
    coordinateSelector (Finset.univ : Finset n) = (1 : Matrix n n 𝕜) := by
  simp [coordinateSelector]

/-- Complementary coordinate selectors are exactly the residual projection. -/
theorem coordinateSelector_compl (S : Finset n) :
    (coordinateSelector Sᶜ : Matrix n n 𝕜) = 1 - coordinateSelector S := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S <;> simp [coordinateSelector, hi]
  · simp [coordinateSelector, hij]

end NLAlib
