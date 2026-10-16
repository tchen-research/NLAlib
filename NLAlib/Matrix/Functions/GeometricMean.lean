import NLAlib.Matrix.Functions.PerspectiveSqrtNormalization
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# The positive-definite-first matrix geometric mean

The geometric mean is the existing matrix perspective of the scalar square
root. Its formula uses ordinary inverses and positive square roots; outside
the positive-definite-first domain it retains the perspective's total CFC
values, without asserting a singular-input extension.
Tropp (2022), Definition 16.15. Atlas: `matrix-geometric-mean-def`.
-/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The geometric mean is the square-root perspective. The intended domain
has positive-definite first input and positive-semidefinite second input;
elsewhere this is the total CFC formula, not a singular extension.
Tropp (2022), Definition 16.15.
atlas: matrix-geometric-mean-def -/
def matrixGeometricMean (A B : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  matrixPerspective Real.sqrt A B

/-- The geometric mean unfolds to the standard square-root congruence. -/
theorem matrixGeometricMean_eq (A B : Matrix n n 𝕜) :
    matrixGeometricMean A B = cfc Real.sqrt A *
      cfc Real.sqrt (cfc (fun x => (Real.sqrt x)⁻¹) A * B *
        cfc (fun x => (Real.sqrt x)⁻¹) A) * cfc Real.sqrt A := rfl

/-- The real square-root functional calculus is positive semidefinite. -/
theorem posSemidef_cfc_sqrt (A : Matrix n n 𝕜) :
    (cfc Real.sqrt A).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg (fun x _ => Real.sqrt_nonneg x))

/-- The geometric-mean formula is positive semidefinite. On its intended
domain this is positivity of the positive-definite-first geometric mean. -/
theorem posSemidef_matrixGeometricMean (A B : Matrix n n 𝕜) :
    (matrixGeometricMean A B).PosSemidef := by
  have hS : (cfc Real.sqrt A).IsHermitian := cfc_predicate _ _
  rw [matrixGeometricMean_eq]
  simpa only [hS.eq] using (posSemidef_cfc_sqrt _).mul_mul_conjTranspose_same
    (cfc Real.sqrt A)

/-- Whitening a positive-definite matrix by its inverse square root gives
the identity. -/
theorem cfc_inv_sqrt_mul_self_mul_inv_sqrt {A : Matrix n n 𝕜} (hA : A.PosDef) :
    cfc (fun x => (Real.sqrt x)⁻¹) A * A *
      cfc (fun x => (Real.sqrt x)⁻¹) A = 1 := by
  calc
    _ = cfc (fun x => (Real.sqrt x)⁻¹) A *
        (cfc Real.sqrt A * cfc Real.sqrt A) *
        cfc (fun x => (Real.sqrt x)⁻¹) A := by
      rw [cfc_sqrt_mul_self hA]
    _ = 1 := by
      rw [← Matrix.mul_assoc, cfc_inv_sqrt_mul_sqrt hA, one_mul,
        cfc_sqrt_mul_inv_sqrt hA]

/-- The positive-definite geometric mean of a matrix with itself is itself. -/
@[simp] theorem matrixGeometricMean_self {A : Matrix n n 𝕜} (hA : A.PosDef) :
    matrixGeometricMean A A = A := by
  rw [matrixGeometricMean_eq, cfc_inv_sqrt_mul_self_mul_inv_sqrt hA]
  have hs : cfc Real.sqrt (1 : Matrix n n 𝕜) = 1 := by simp
  rw [hs, Matrix.mul_one, cfc_sqrt_mul_self hA]

end NLAlib
