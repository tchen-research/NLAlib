import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Exact tangent remainders of positive matrix inversion

The inverse tangent error is a genuine positive congruence, without any
commutativity or order-comparability assumption on the two matrices.
-/

noncomputable section
set_option autoImplicit false
open scoped MatrixOrder ComplexOrder
namespace Matrix
variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The exact native inverse tangent remainder at the second point is
a quadratic sandwich of the first inverse. -/
theorem inv_sub_inv_sub_tangent_eq (A B : Matrix n n 𝕜) (hA : IsUnit A) (hB : IsUnit B) :
    A⁻¹-B⁻¹-B⁻¹*(B-A)*B⁻¹=B⁻¹*(B-A)*A⁻¹*(B-A)*B⁻¹ := by
  have he : B⁻¹*(B-A)*A⁻¹=A⁻¹-B⁻¹ := by
    rw [Matrix.mul_sub,Matrix.sub_mul,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hB),Matrix.one_mul,
      Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
      Matrix.mul_one]
  calc
    _ = (B⁻¹*(B-A)*A⁻¹)-(B⁻¹*(B-A)*B⁻¹) := by rw [he]
    _ = B⁻¹*(B-A)*(A⁻¹-B⁻¹) := (Matrix.mul_sub _ _ _).symm
    _ = _ := by
      rw [Matrix.inv_sub_inv ⟨fun _ => hB,fun _ => hA⟩]
      simp only [Matrix.mul_assoc]

/-- The inverse tangent lies below the actual inverse difference at two
positive definite matrices. This is operator convexity in a form that
retains the genuine noncommutative derivative. -/
theorem PosDef.inv_tangent_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef) :
    B⁻¹*(B-A)*B⁻¹≤A⁻¹-B⁻¹ := by
  apply Matrix.le_iff.mpr
  rw [inv_sub_inv_sub_tangent_eq A B hA.isUnit hB.isUnit]
  have hC : (B-A).IsHermitian := hB.isHermitian.sub hA.isHermitian
  have hP := hA.inv.posSemidef.mul_mul_conjTranspose_same (B⁻¹*(B-A))
  simpa only [Matrix.conjTranspose_mul,hC.eq,hB.inv.isHermitian.eq,Matrix.mul_assoc] using hP

end Matrix
