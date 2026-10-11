import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NLAlib.Matrix.ComplexVolumeProjection

/-!
# The canonical full-row-rank complex right inverse

For a full-row-rank native complex matrix `B`, its row Gram is invertible and
the standard Moore--Penrose expression `Bᴴ (B Bᴴ)⁻¹` is a right inverse.
Source: HMT (2011), §A.2; Horn--Johnson, §7.3; manuscript `sa:filter`.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {k t : Type*} [Fintype k] [Fintype t] [DecidableEq k]

/-- Full native complex row rank makes the actual row Gram invertible.
Source: Gram rank and finite-dimensional surjectivity; manuscript `sa:filter`. -/
theorem isUnit_mul_conjTranspose_of_rank_eq_card
    (B : Matrix k t ℂ) (hB : B.rank = Fintype.card k) : IsUnit (B * Bᴴ) := by
  have htop : LinearMap.range (B * Bᴴ).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change (B * Bᴴ).rank = Module.finrank ℂ (k → ℂ)
    rw [Matrix.rank_self_mul_conjTranspose, hB, Module.finrank_fintype_fun_eq_card]
  exact Matrix.mulVec_surjective_iff_isUnit.mp (LinearMap.range_eq_top.mp htop)

/-- The canonical full-row-rank complex pseudoinverse expression is a right inverse.
Its certificate is derived from native full row rank, rather than assumed.
Source: HMT (2011), §A.2; Horn--Johnson, §7.3; manuscript `sa:filter`. -/
theorem mul_conjTranspose_mul_inv_gram_eq_one_of_rank_eq_card
    (B : Matrix k t ℂ) (hB : B.rank = Fintype.card k) :
    B * (Bᴴ * (B * Bᴴ)⁻¹) = 1 := by
  have hG := isUnit_mul_conjTranspose_of_rank_eq_card B hB
  rw [← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hG)]

end NLAlib
