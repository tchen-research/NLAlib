import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Loewner order under Kronecker products

Positive tensor factors preserve the finite matrix order. These order
bridges are shared by tensor compressions and matrix-valued polynomial models.
-/

noncomputable section
open scoped MatrixOrder Kronecker ComplexOrder
namespace Matrix
variable {𝕜 m n : Type*} [RCLike 𝕜]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Tensoring on the right by a PSD matrix preserves Loewner order. -/
theorem kronecker_le_kronecker_right {A B : Matrix m m 𝕜} {C : Matrix n n 𝕜}
    (hAB : A ≤ B) (hC : C.PosSemidef) : A ⊗ₖ C ≤ B ⊗ₖ C := by
  apply Matrix.le_iff.mpr
  have he : B ⊗ₖ C - A ⊗ₖ C = (B - A) ⊗ₖ C := by
    ext a b
    simp [Matrix.kronecker_apply, sub_mul]
  rw [he]
  exact (Matrix.le_iff.mp hAB).kronecker hC

/-- Tensoring on the left by a PSD matrix preserves Loewner order. -/
theorem kronecker_le_kronecker_left {A B : Matrix n n 𝕜} {C : Matrix m m 𝕜}
    (hAB : A ≤ B) (hC : C.PosSemidef) : C ⊗ₖ A ≤ C ⊗ₖ B := by
  apply Matrix.le_iff.mpr
  have he : C ⊗ₖ B - C ⊗ₖ A = C ⊗ₖ (B - A) := by
    ext a b
    simp [Matrix.kronecker_apply, mul_sub]
  rw [he]
  exact hC.kronecker (Matrix.le_iff.mp hAB)

/-- Rectangular congruence preserves the Loewner order. -/
theorem conjTranspose_mul_le_conjTranspose_mul {A B : Matrix m m 𝕜}
    (hAB : A ≤ B) (C : Matrix m n 𝕜) : Cᴴ * A * C ≤ Cᴴ * B * C := by
  apply Matrix.le_iff.mpr
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  exact (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same C

/-- Multiplication by a nonnegative real scalar preserves Loewner order.
This uses the PSD cone directly rather than a pointwise matrix order. -/
theorem real_smul_le_real_smul {A B : Matrix n n 𝕜} (hAB : A ≤ B)
    {r : ℝ} (hr : 0 ≤ r) : r • A ≤ r • B := by
  apply Matrix.le_iff.mpr
  rw [← smul_sub]
  exact (Matrix.le_iff.mp hAB).smul hr

end Matrix
