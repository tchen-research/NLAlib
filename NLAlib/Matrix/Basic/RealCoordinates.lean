import NLAlib.ForMathlib.Analysis.ComplexCoordinates
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Full real coordinates of complex matrices

The coordinate space retains every real and imaginary entry. Thus matching
its scalar covariance matrix means full real covariance matching, including
mixed real/imaginary covariances.
-/

noncomputable section
namespace NLAlib
variable {m n : Type*}

/-- Flatten all real and imaginary entries into disjoint real coordinates. -/
def matrixRealCoordinates : Matrix m n ℂ ≃ₗ[ℝ] ((m × n) ⊕ (m × n) → ℝ) where
  toFun A := Complex.realCoordinates (m×n) (fun ij => A ij.1 ij.2)
  invFun x i j := (Complex.realCoordinates (m×n)).symm x (i,j)
  left_inv A := by
    funext i j
    exact congrFun ((Complex.realCoordinates (m×n)).symm_apply_apply (fun ij => A ij.1 ij.2)) (i,j)
  right_inv x := (Complex.realCoordinates (m×n)).apply_symm_apply x
  map_add' A B := (Complex.realCoordinates (m×n)).map_add
    (fun ij => A ij.1 ij.2) (fun ij => B ij.1 ij.2)
  map_smul' c A := (Complex.realCoordinates (m×n)).map_smul c (fun ij => A ij.1 ij.2)

@[simp] theorem matrixRealCoordinates_inl (A : Matrix m n ℂ) (i : m) (j : n) :
    matrixRealCoordinates A (Sum.inl (i,j)) = (A i j).re := rfl

@[simp] theorem matrixRealCoordinates_inr (A : Matrix m n ℂ) (i : m) (j : n) :
    matrixRealCoordinates A (Sum.inr (i,j)) = (A i j).im := rfl

open scoped Matrix.Norms.L2Operator in
/-- The full real matrix-coordinate map is a continuous linear equivalence. -/
def matrixRealCoordinatesContinuousLinearEquiv [Fintype m] [Fintype n] [DecidableEq n] :
    Matrix m n ℂ ≃L[ℝ] ((m×n) ⊕ (m×n) → ℝ) :=
  matrixRealCoordinates.toContinuousLinearEquiv

open scoped Matrix.Norms.L2Operator in
/-- Full real and imaginary matrix-entry coordinates depend continuously on
all entries. -/
@[fun_prop] theorem continuous_matrixRealCoordinates
    [Fintype m] [Fintype n] [DecidableEq n] :
    Continuous (matrixRealCoordinates : Matrix m n ℂ → ((m × n) ⊕ (m × n) → ℝ)) :=
  matrixRealCoordinatesContinuousLinearEquiv.continuous

/-- Full real matrix-entry coordinates are measurable. -/
@[fun_prop] theorem measurable_matrixRealCoordinates
    [Fintype m] [Fintype n] [DecidableEq n] :
    Measurable (matrixRealCoordinates : Matrix m n ℂ → ((m × n) ⊕ (m × n) → ℝ)) :=
  continuous_matrixRealCoordinates.measurable

end NLAlib
