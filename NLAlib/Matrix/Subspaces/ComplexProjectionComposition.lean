import NLAlib.Matrix.Subspaces.ComplexProjectionBounds
/-!
# Nested actual complex column projectors

Containment of one complex column range in another makes the projectors compose
and gives monotone spectral and Frobenius residual errors. Source: Hilbert orthogonal
projection; manuscript `sa:filter`, block Krylov specialization.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq l]

/-- A containing actual complex column space has no larger spectral residual.
Source: projection contraction; manuscript `sa:filter`, block Krylov specialization. -/
theorem norm_sub_rangeProjector_mul_le_of_mul_eq
    (Q : Matrix m k ℂ) (Y : Matrix m l ℂ)
    (h : rangeProjector Q * Y = Y) (A : Matrix m n ℂ) :
    ‖A - rangeProjector Q * A‖ ≤ ‖A - rangeProjector Y * A‖ := by
  have hp := rangeProjector_mul_rangeProjector_of_mul_eq h
  have he : A - rangeProjector Q * A =
      (A - rangeProjector Y * A) -
        rangeProjector Q * (A - rangeProjector Y * A) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hp]
    abel
  rw [he]
  exact norm_sub_rangeProjector_mul_le _ _

section Frobenius
open scoped Matrix.Norms.Frobenius

omit [DecidableEq n] in
/-- A containing actual complex column space has no larger squared Frobenius
residual. Source: projection contraction; manuscript `sa:filter`. -/
theorem frobenius_norm_sub_rangeProjector_mul_sq_le_of_mul_eq
    (Q : Matrix m k ℂ) (Y : Matrix m l ℂ)
    (h : rangeProjector Q * Y = Y) (A : Matrix m n ℂ) :
    ‖A - rangeProjector Q * A‖ ^ 2 ≤ ‖A - rangeProjector Y * A‖ ^ 2 := by
  have hp := rangeProjector_mul_rangeProjector_of_mul_eq h
  have he : A - rangeProjector Q * A =
      (A - rangeProjector Y * A) -
        rangeProjector Q * (A - rangeProjector Y * A) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hp]
    abel
  rw [he]
  exact frobenius_norm_sub_rangeProjector_mul_sq_le _ _

end Frobenius
end NLAlib
