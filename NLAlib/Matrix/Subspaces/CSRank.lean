import NLAlib.Matrix.Basic.ComplementaryRank
import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!
# Ranks of complementary orthogonal blocks

The complementary-right-nullity law gives the rank consequences of CS
decomposition without requiring its canonical form. Horn–Johnson 2013,
Lemma 2.1.10; atlas `cs-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

private def sumNotLeftEquiv (p q : Type*) : {s : p ⊕ q // ¬s.isLeft} ≃ q :=
  (Equiv.subtypeEquivRight (fun s : p ⊕ q => by cases s <;> simp)).trans Equiv.sumIsRight

private def sumNotRightEquiv (p q : Type*) : {s : p ⊕ q // ¬s.isRight} ≃ p :=
  (Equiv.subtypeEquivRight (fun s : p ⊕ q => by cases s <;> simp)).trans Equiv.sumIsLeft

private theorem rank_toBlock_of_equiv {N m n : Type*} [Fintype N] [Fintype m] [Fintype n]
    (A : Matrix N N ℝ) (p q : N → Prop) [DecidablePred p] [DecidablePred q]
    (ep : {i // p i} ≃ m) (eq : {j // q j} ≃ n) :
    (A.toBlock p q).rank = (A.submatrix (fun i => (ep.symm i).val) (fun j => (eq.symm j).val)).rank := by
  exact (Matrix.rank_submatrix (A.toBlock p q) ep.symm eq.symm).symm

private theorem inverse_eq_transpose_of_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℝ} (hU : HasOrthonormalCols U) : IsUnit U.det ∧ U⁻¹ = Uᵀ := by
  have hDet : U.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det hU.transpose_mul_self
    rw [Matrix.det_mul, Matrix.det_transpose, hz, mul_zero, Matrix.det_one] at h
    exact zero_ne_one h
  have hUnit := isUnit_iff_ne_zero.mpr hDet
  refine ⟨hUnit, ?_⟩
  calc
    U⁻¹ = (Uᵀ * U) * U⁻¹ := by rw [hU.transpose_mul_self, Matrix.one_mul]
    _ = Uᵀ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv U hUnit, Matrix.mul_one]

/-- The two off-diagonal blocks of a real square orthogonal matrix have
equal rank, with arbitrary finite block labels. Horn–Johnson 2013, Lemma 2.1.10.
atlas: cs-decomposition (partial) -/
theorem rank_offDiagonal_blocks_eq_of_orthogonal {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (U : Matrix (p ⊕ q) (p ⊕ q) ℝ) (hU : HasOrthonormalCols U) :
    U.toBlocks₁₂.rank = U.toBlocks₂₁.rank := by
  obtain ⟨hUnit, hInv⟩ := inverse_eq_transpose_of_orthogonal hU
  have h := card_columns_sub_rank_toBlock_eq_inverse_complement U hUnit
    (fun s => s.isLeft) (fun s => s.isRight)
  have h12 : (U.toBlock (fun s => s.isLeft) (fun s => s.isRight)).rank = U.toBlocks₁₂.rank := by
    exact rank_toBlock_of_equiv U _ _ Equiv.sumIsLeft Equiv.sumIsRight
  have hInv12 : (U⁻¹.toBlock (fun s => ¬s.isRight) (fun s => ¬s.isLeft)).rank =
      U.toBlocks₂₁.rank := by
    rw [rank_toBlock_of_equiv U⁻¹ _ _ (sumNotRightEquiv p q) (sumNotLeftEquiv p q), hInv]
    change U.toBlocks₂₁ᵀ.rank = U.toBlocks₂₁.rank
    exact Matrix.rank_transpose _
  rw [h12, hInv12, Fintype.card_congr (Equiv.sumIsRight : {s : p ⊕ q // s.isRight} ≃ q),
    Fintype.card_congr (sumNotLeftEquiv p q)] at h
  have h12le := U.toBlocks₁₂.rank_le_card_width
  have h21le := U.toBlocks₂₁.rank_le_card_height
  omega

/-- The lower-right block rank is the upper-left rank plus the difference
of the block dimensions when the first block is no larger. Horn–Johnson
2013, Lemma 2.1.10. Empty blocks are included.
atlas: cs-decomposition (partial) -/
theorem rank_bottomRight_eq_rank_topLeft_add_card_sub_of_orthogonal {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (U : Matrix (p ⊕ q) (p ⊕ q) ℝ) (hU : HasOrthonormalCols U)
    (hCard : Fintype.card p ≤ Fintype.card q) :
    U.toBlocks₂₂.rank = U.toBlocks₁₁.rank + Fintype.card q - Fintype.card p := by
  obtain ⟨hUnit, hInv⟩ := inverse_eq_transpose_of_orthogonal hU
  have h := card_columns_sub_rank_toBlock_eq_inverse_complement U hUnit
    (fun s => s.isLeft) (fun s => s.isLeft)
  have h11 : (U.toBlock (fun s => s.isLeft) (fun s => s.isLeft)).rank = U.toBlocks₁₁.rank :=
    rank_toBlock_of_equiv U _ _ Equiv.sumIsLeft Equiv.sumIsLeft
  have hInv22 : (U⁻¹.toBlock (fun s => ¬s.isLeft) (fun s => ¬s.isLeft)).rank =
      U.toBlocks₂₂.rank := by
    rw [rank_toBlock_of_equiv U⁻¹ _ _ (sumNotLeftEquiv p q) (sumNotLeftEquiv p q), hInv]
    change U.toBlocks₂₂ᵀ.rank = U.toBlocks₂₂.rank
    exact Matrix.rank_transpose _
  rw [h11, hInv22, Fintype.card_congr (Equiv.sumIsLeft : {s : p ⊕ q // s.isLeft} ≃ p),
    Fintype.card_congr (sumNotLeftEquiv p q)] at h
  have h11le := U.toBlocks₁₁.rank_le_card_width
  have h22le := U.toBlocks₂₂.rank_le_card_width
  omega

end NLAlib
