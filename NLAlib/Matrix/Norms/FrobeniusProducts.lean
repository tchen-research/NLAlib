import NLAlib.Matrix.Norms.Frobenius

/-!
# Adjoint identities for the Frobenius pairing

Left and right matrix multiplication move across the real Frobenius pairing
by taking the adjoint. These identities support rectangular Galerkin equations
and their energy-minimization interpretation.
-/

noncomputable section

open scoped Matrix
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-- Left matrix multiplication is adjoint to left multiplication by the adjoint. -/
theorem frobInner_mul_left (A : Matrix m p 𝕜) (X : Matrix p n 𝕜) (Y : Matrix m n 𝕜) :
    frobInner (A * X) Y = frobInner X (Aᴴ * Y) := by
  rw [frobInner_eq_trace, frobInner_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Right multiplication by an adjoint is adjoint to ordinary right multiplication. -/
theorem frobInner_mul_right (X : Matrix m p 𝕜) (B : Matrix n p 𝕜) (Y : Matrix m n 𝕜) :
    frobInner (X * Bᴴ) Y = frobInner X (Y * B) := by
  rw [frobInner_eq_trace, frobInner_eq_trace, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.trace_mul_comm B,
    Matrix.mul_assoc]

/-- A two-sided trial matrix pairs with a residual through the reduced residual. -/
theorem frobInner_mul_mul_conjTranspose (V : Matrix m p 𝕜) (T : Matrix p q 𝕜)
    (W : Matrix n q 𝕜) (R : Matrix m n 𝕜) :
    frobInner (V * T * Wᴴ) R = frobInner T (Vᴴ * R * W) := by
  rw [frobInner_mul_right, frobInner_mul_left, Matrix.mul_assoc]

end NLAlib
