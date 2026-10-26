import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Real.Basic

/-!
# Schur-complement rank additivity

Invertible block elimination preserves rank and turns the matrix into a block
diagonal map. No symmetry or invertibility of the trailing block is required.
Horn–Johnson 2013, §0.8.4; atlas `complementary-nullities`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
/-- A rectangular block diagonal matrix has rank equal to the sum of its
two block ranks. Horn–Johnson §0.4; Schur-rank helper. -/
theorem rank_fromBlocks_zero_zero_eq {K m n p q : Type*} [Field K]
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m p K) (D : Matrix n q K) :
    (Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  let e : LinearMap.ker (Matrix.fromBlocks A 0 0 D).mulVecLin ≃ₗ[K]
      (LinearMap.ker A.mulVecLin × LinearMap.ker D.mulVecLin) :=
    { toFun := fun x =>
        (⟨fun j => x.val (Sum.inl j), by
          funext i
          have h := congrFun x.property (Sum.inl i)
          simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
            Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
            Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Pi.zero_apply] using h⟩,
        ⟨fun j => x.val (Sum.inr j), by
          funext i
          have h := congrFun x.property (Sum.inr i)
          simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
            Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
            Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Pi.zero_apply] using h⟩)
      invFun := fun x => ⟨Sum.elim x.1.val x.2.val, by
        funext i
        cases i with
        | inl i =>
          have h := congrFun x.1.property i
          simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
            Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
            Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Sum.elim_inl, Pi.zero_apply] using h
        | inr i =>
          have h := congrFun x.2.property i
          simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
            Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
            Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Sum.elim_inr, Pi.zero_apply] using h⟩
      left_inv := by intro x; apply Subtype.ext; funext i; cases i <;> rfl
      right_inv := by intro x; apply Prod.ext <;> apply Subtype.ext <;> rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have hK := e.finrank_eq
  rw [Module.finrank_prod] at hK
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hD := D.mulVecLin.finrank_range_add_finrank_ker
  have hAD := (Matrix.fromBlocks A 0 0 D).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hA hD hAD
  rw [Fintype.card_sum] at hAD
  change A.rank + _ = _ at hA
  change D.rank + _ = _ at hD
  change (Matrix.fromBlocks A 0 0 D).rank + _ = _ at hAD
  omega

/-- An invertible leading block contributes its full rank, and the remaining
rank is exactly the Schur-complement rank. Rectangular trailing blocks,
singular Schur complements and empty blocks are included. Horn–Johnson 2013,
§0.8.4.
atlas: complementary-nullities (partial) -/
theorem rank_fromBlocks_eq_rank_add_rank_schur {m n l : Type*}
    [Fintype m] [Fintype n] [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq l]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix l m ℝ) (D : Matrix l n ℝ)
    (hA : IsUnit A.det) :
    (Matrix.fromBlocks A B C D).rank = A.rank + (D - C * A⁻¹ * B).rank := by
  let := A.invertibleOfIsUnitDet hA
  have hFactor := Matrix.fromBlocks_eq_of_invertible₁₁ A B C D
  rw [Matrix.invOf_eq_nonsing_inv] at hFactor
  have hLeft : IsUnit (Matrix.fromBlocks (1 : Matrix m m ℝ) 0 (C * A⁻¹)
      (1 : Matrix l l ℝ)).det := by
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, one_mul]
    exact isUnit_one
  have hRight : IsUnit (Matrix.fromBlocks (1 : Matrix m m ℝ) (A⁻¹ * B) 0
      (1 : Matrix n n ℝ)).det := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]
    exact isUnit_one
  rw [hFactor, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hRight,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hLeft, rank_fromBlocks_zero_zero_eq]

end NLAlib
