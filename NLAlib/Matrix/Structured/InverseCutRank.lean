import NLAlib.Matrix.Basic.ComplementaryRank

/-!
# Off-diagonal cut ranks of an inverse

Complementary nullities imply that an inverse preserves the rank of every
whole off-diagonal cut, without any invertible principal-block hypothesis.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Inverting a square matrix preserves the rank of either directed whole
off-diagonal cut. Source: complementary nullities, and the HSS inverse-rank
derivation. No principal diagonal block is required to be invertible.
atlas: hss-inverse-rank-preservation (partial) -/
theorem rank_inverse_toBlock_complement_eq {K n : Type*} [Field K]
    [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : IsUnit A.det)
    (p : n → Prop) [DecidablePred p] :
    (A⁻¹.toBlock p (fun i => ¬p i)).rank = (A.toBlock p (fun i => ¬p i)).rank := by
  classical
  have h := card_columns_sub_rank_toBlock_eq_inverse_complement A hA p (fun i => ¬p i)
  have heq : (A⁻¹.toBlock (fun i => ¬¬p i) (fun i => ¬p i)).rank =
      (A⁻¹.toBlock p (fun i => ¬p i)).rank := by
    let e : {i // p i} ≃ {i // ¬¬p i} :=
      ⟨fun i => ⟨i, not_not.mpr i.property⟩, fun i => ⟨i, not_not.mp i.property⟩,
        fun _ => rfl, fun _ => rfl⟩
    exact (Matrix.rank_submatrix _ e (Equiv.refl _)).symm
  rw [heq] at h
  have h₁ := (A.toBlock p (fun i => ¬p i)).rank_le_card_width
  have h₂ := (A⁻¹.toBlock p (fun i => ¬p i)).rank_le_card_width
  omega

end NLAlib
