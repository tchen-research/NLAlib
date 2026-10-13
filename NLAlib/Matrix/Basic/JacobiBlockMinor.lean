import NLAlib.Matrix.Basic.ComplementaryRank
import NLAlib.Matrix.Basic.Gram
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Jacobi's complementary-minor identity for block coordinates

Singular selected blocks have singular complementary inverse blocks by the
right-nullity law. The nonsingular case is the Schur inverse formula.
This includes all singular subminors and empty blocks without limits.
Horn–Johnson 2013, §§0.7.5–0.7.6 and 0.8.4.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
private def complementEquiv (p q : Type*) : {s : p ⊕ q // ¬s.isLeft} ≃ q :=
  (Equiv.subtypeEquivRight (fun s : p ⊕ q => by cases s <;> simp)).trans Equiv.sumIsRight

private theorem card_sub_rank_blocks_eq {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (M : Matrix (p ⊕ q) (p ⊕ q) ℝ) (hM : IsUnit M.det) :
    Fintype.card p - M.toBlocks₁₁.rank = Fintype.card q - M⁻¹.toBlocks₂₂.rank := by
  have h := card_columns_sub_rank_toBlock_eq_inverse_complement M hM
    (fun s => s.isLeft) (fun s => s.isLeft)
  have hFirst : (M.toBlock (fun s => s.isLeft) (fun s => s.isLeft)).rank = M.toBlocks₁₁.rank :=
    (Matrix.rank_submatrix (M.toBlock (fun s => s.isLeft) (fun s => s.isLeft))
      Equiv.sumIsLeft.symm Equiv.sumIsLeft.symm).symm
  have hLast : (M⁻¹.toBlock (fun s => ¬s.isLeft) (fun s => ¬s.isLeft)).rank = M⁻¹.toBlocks₂₂.rank :=
    (Matrix.rank_submatrix (M⁻¹.toBlock (fun s => ¬s.isLeft) (fun s => ¬s.isLeft))
      (complementEquiv p q).symm (complementEquiv p q).symm).symm
  rwa [hFirst, hLast,
    Fintype.card_congr (Equiv.sumIsLeft : {s : p ⊕ q // s.isLeft} ≃ p),
    Fintype.card_congr (complementEquiv p q)] at h

/-- A singular leading selected block forces a singular complementary block
of the inverse of a nonsingular ambient matrix. Horn–Johnson §0.7.6;
Jacobi identity helper, including empty blocks. -/
theorem det_inverse_bottomRight_eq_zero_of_topLeft_eq_zero {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (M : Matrix (p ⊕ q) (p ⊕ q) ℝ) (hM : IsUnit M.det) (hZero : M.toBlocks₁₁.det = 0) :
    M⁻¹.toBlocks₂₂.det = 0 := by
  by_contra hLast
  have h := card_sub_rank_blocks_eq M hM
  have hRank := Matrix.rank_of_det_ne_zero hLast
  rw [hRank, Nat.sub_self] at h
  have hBound := M.toBlocks₁₁.rank_le_card_width
  have hFull : M.toBlocks₁₁.rank = Fintype.card p := by omega
  exact det_ne_zero_of_rank_eq M.toBlocks₁₁ hFull hZero

/-- Jacobi's inverse-minor formula in block coordinates: the determinant of
the complementary inverse block is the selected-block determinant divided
by the ambient determinant. The selected block can be singular and either
block can be empty. Horn–Johnson 2013, §§0.7.6 and 0.8.4.
atlas: complementary-nullities (partial) -/
theorem det_inverse_bottomRight_eq_topLeft_div_det {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (M : Matrix (p ⊕ q) (p ⊕ q) ℝ) (hM : IsUnit M.det) :
    M⁻¹.toBlocks₂₂.det = M.toBlocks₁₁.det / M.det := by
  by_cases hZero : M.toBlocks₁₁.det = 0
  · rw [det_inverse_bottomRight_eq_zero_of_topLeft_eq_zero M hM hZero, hZero, zero_div]
  · let A := M.toBlocks₁₁
    let B := M.toBlocks₁₂
    let C := M.toBlocks₂₁
    let D := M.toBlocks₂₂
    let S := D - C * A⁻¹ * B
    have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hZero
    let := A.invertibleOfIsUnitDet hA
    have hFactor : M = Matrix.fromBlocks A B C D := (Matrix.fromBlocks_toBlocks M).symm
    have hDet : M.det = A.det * S.det := by
      rw [hFactor, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    have hS : IsUnit S.det := by
      apply isUnit_iff_ne_zero.mpr
      intro hz
      exact hM.ne_zero (by rw [hDet, hz, mul_zero])
    let := S.invertibleOfIsUnitDet hS
    have hMBlock : IsUnit (Matrix.fromBlocks A B C D).det := by rw [← hFactor]; exact hM
    let := (Matrix.fromBlocks A B C D).invertibleOfIsUnitDet hMBlock
    have hInv := Matrix.invOf_fromBlocks₁₁_eq A B C D
    simp only [Matrix.invOf_eq_nonsing_inv] at hInv
    have hCorner : M⁻¹.toBlocks₂₂ = S⁻¹ := by
      rw [hFactor, hInv]
      rfl
    rw [hCorner, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hDet]
    have hAn : A.det ≠ 0 := isUnit_iff_ne_zero.mp hA
    have hSn : S.det ≠ 0 := isUnit_iff_ne_zero.mp hS
    field_simp
    rfl

end NLAlib
