import NLAlib.Matrix.Functions.RidgeKernel
import NLAlib.Matrix.Subspaces.RangeProjector

/-!
# Ridge kernels on the sampled range

The ridge kernel lies below the projector onto the matrix range. Consequently the
complementary range projector is below the scaled inverse regularized row Gram matrix.
These deterministic identities feed the regularized-approximation range-error theorem.

Source: Chenakkod–Dereziński 2026, Lemma 3.3; the finite projection derivation is in
`sketching_lowrank_routes_2026_10_24/sketching.tex`, regularized range-error section.
Atlas: `regularized-approximation-range-error` (shared matrix analysis).
-/

noncomputable section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A ridge kernel is below the ordinary projector onto the matrix range. This follows
from positivity, contraction, and the identity that the range projector fixes the kernel. -/
theorem ridgeKernel_le_rangeProjector (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ridgeKernel A ρ ≤ rangeProjector A := by
  let P := rangeProjector A
  have hP : P.IsHermitian := rangeProjector_isHermitian A
  have hPP : P * P = P := rangeProjector_isIdempotentElem A
  have hK : (ridgeKernel A ρ).IsHermitian := (posSemidef_ridgeKernel A hρ).isHermitian
  have hPK : P * ridgeKernel A ρ = ridgeKernel A ρ := by
    calc
      P * ridgeKernel A ρ = (P * A) * (ridgeGram A ρ)⁻¹ * Aᵀ := by
        simp only [ridgeKernel, Matrix.mul_assoc]
      _ = ridgeKernel A ρ := by
        rw [show P * A = A from rangeProjector_mul A]
        rfl
  have hKP : ridgeKernel A ρ * P = ridgeKernel A ρ := by
    have h := congrArg Matrix.conjTranspose hPK
    simpa only [Matrix.conjTranspose_mul, hP.eq, hK.eq] using h
  have hp := (Matrix.le_iff.mp (ridgeKernel_le_one A hρ)).mul_mul_conjTranspose_same P
  have heq : P * (1 - ridgeKernel A ρ) * Pᴴ = P - ridgeKernel A ρ := by
    rw [hP.eq, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hPP, hPK, hKP]
  rw [heq] at hp
  exact Matrix.le_iff.mpr hp

/-- The complementary range projector is dominated by the scaled inverse regularized
row Gram matrix. No lower bound on any nonzero singular value is needed. -/
theorem one_sub_rangeProjector_le_smul_inv_ridgeGram (A : Matrix m n ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    1 - rangeProjector A ≤ ρ • (ridgeGram Aᵀ ρ)⁻¹ := by
  apply Matrix.le_iff.mpr
  have hp := Matrix.le_iff.mp (ridgeKernel_le_rangeProjector A hρ)
  rw [ridgeKernel_eq_one_sub_smul_inv A hρ] at hp
  convert hp using 1
  abel

end NLAlib
