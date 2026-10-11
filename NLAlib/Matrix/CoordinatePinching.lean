import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Finite coordinate pinching

Coordinate sign reflections remove the off-diagonal entries in one row and column.
Pinching every coordinate leaves exactly the original diagonal. These are the finite
algebraic steps of the Lieb-concavity proof of Golden–Thompson.
Source: Bhatia 1997, Chapter IX.3; atlas `golden-thompson` (pinching helpers).
-/

noncomputable section
set_option autoImplicit false

namespace NLAlib
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal unitary that changes the sign of coordinate `k`.
Bhatia 1997, IX.3; atlas `golden-thompson` (coordinate reflection). -/
def coordinateReflection (k : ι) : Matrix ι ι ℂ :=
  diagonal fun i => if i = k then -1 else 1

omit [Fintype ι] in
/-- A coordinate reflection is self-adjoint.
Bhatia 1997, IX.3; atlas `golden-thompson` (pinching helper). -/
theorem conjTranspose_coordinateReflection (k : ι) :
    (coordinateReflection k)ᴴ = coordinateReflection k := by
  simp only [coordinateReflection, diagonal_conjTranspose]
  congr 1
  ext i
  by_cases h : i = k <;> simp [h]

/-- A coordinate reflection squares to the identity.
Bhatia 1997, IX.3; atlas `golden-thompson` (pinching helper). -/
theorem coordinateReflection_mul_self (k : ι) :
    coordinateReflection k * coordinateReflection k = 1 := by
  rw [coordinateReflection, diagonal_mul_diagonal]
  ext i j
  by_cases h : i = k <;> simp [diagonal, h, one_apply]

/-- A coordinate reflection fixes every diagonal matrix by conjugation.
Bhatia 1997, IX.3; atlas `golden-thompson` (pinching helper). -/
theorem coordinateReflection_mul_diagonal_mul (k : ι) (a : ι → ℂ) :
    coordinateReflection k * diagonal a * coordinateReflection k = diagonal a := by
  rw [coordinateReflection, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext i
  by_cases h : i = k <;> simp [h]

/-- Midpoint averaging with a coordinate sign reflection.
Bhatia 1997, IX.3; atlas `golden-thompson` (pinching helper). -/
def coordinatePinch (k : ι) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℝ) • X + (1 / 2 : ℝ) •
    (coordinateReflection k * X * coordinateReflection k)

/-- A coordinate pinch keeps the diagonal and the untouched block, and kills
the other entries in its row and column. Bhatia 1997, IX.3;
atlas `golden-thompson` (entrywise pinching formula). -/
theorem coordinatePinch_apply (k : ι) (X : Matrix ι ι ℂ) (i j : ι) :
    coordinatePinch k X i j = if i = j ∨ i ≠ k ∧ j ≠ k then X i j else 0 := by
  simp only [coordinatePinch, coordinateReflection, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.real_smul]
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k <;> simp [hik] <;> ring
  · by_cases hik : i = k <;> by_cases hjk : j = k <;>
      simp_all [eq_comm]
    ring

/-- The explicit matrix obtained by pinching the coordinates in `s`.
Bhatia 1997, IX.3; atlas `golden-thompson` (finite pinching). -/
def coordinatePinched (s : Finset ι) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if i = j ∨ i ∉ s ∧ j ∉ s then X i j else 0

omit [Fintype ι] in
/-- Pinching no coordinates leaves a matrix unchanged.
Bhatia 1997, IX.3; atlas `golden-thompson` (finite pinching helper). -/
@[simp] theorem coordinatePinched_empty (X : Matrix ι ι ℂ) :
    coordinatePinched ∅ X = X := by
  ext i j
  simp [coordinatePinched]

/-- Adding a coordinate to the pinched set is exactly one more midpoint pinch.
Bhatia 1997, IX.3; atlas `golden-thompson` (finite pinching induction). -/
theorem coordinatePinched_insert (s : Finset ι) (k : ι) (X : Matrix ι ι ℂ) :
    coordinatePinched (insert k s) X = coordinatePinch k (coordinatePinched s X) := by
  ext i j
  rw [coordinatePinch_apply]
  by_cases hij : i = j
  · subst j; simp [coordinatePinched]
  · by_cases hik : i = k <;> by_cases hjk : j = k <;>
      by_cases his : i ∈ s <;> by_cases hjs : j ∈ s <;>
      simp_all [coordinatePinched, eq_comm]

/-- Pinching every coordinate leaves the original diagonal.
Bhatia 1997, IX.3; atlas `golden-thompson` (finite pinching endpoint). -/
@[simp] theorem coordinatePinched_univ (X : Matrix ι ι ℂ) :
    coordinatePinched Finset.univ X = diagonal (fun i => X i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [coordinatePinched, diagonal]
  · simp [coordinatePinched, diagonal, hij]

omit [Fintype ι] in
/-- Pinching any coordinates preserves every diagonal entry.
Bhatia 1997, IX.3; atlas `golden-thompson` (finite pinching helper). -/
@[simp] theorem coordinatePinched_apply_self (s : Finset ι) (X : Matrix ι ι ℂ) (i : ι) :
    coordinatePinched s X i i = X i i := by
  simp [coordinatePinched]

end NLAlib
