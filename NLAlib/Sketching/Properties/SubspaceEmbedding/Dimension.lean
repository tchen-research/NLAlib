import NLAlib.Matrix.Basic.LeastSquares
import NLAlib.Sketching.Properties.SubspaceEmbedding.SubspaceEmbedding

/-!
# The dimension obstruction for subspace embeddings

An embedding of a nonzero orthonormal column space at distortion strictly below one needs at
least as many sketch rows as the dimension of that space.
-/

noncomputable section

open Matrix

namespace NLAlib

/-- A subspace embedding at distortion below one has at least as many rows as orthonormal
columns in the embedded space. -/
theorem IsSubspaceEmbedding.card_le {m n r : Type*} [Fintype m] [Fintype n]
    [Fintype r] [DecidableEq r] {S : Matrix m n ℝ} {U : Matrix n r ℝ} {ε : ℝ}
    (h : IsSubspaceEmbedding S U ε) (hU : HasOrthonormalCols U) (hε : ε < 1) :
    Fintype.card r ≤ Fintype.card m := by
  classical
  have hrank : (S * U).rank = Fintype.card r := by
    apply (rank_eq_card_iff_forall_mulVec_eq_zero (S * U)).2
    intro x hx
    have hlo := ((isSubspaceEmbedding_iff_of_hasOrthonormalCols hU).1 h x).1
    rw [hx, dotProduct_zero] at hlo
    have hq : x ⬝ᵥ x ≤ 0 := by
      have hp : 0 < 1 - ε := by linarith
      nlinarith
    exact dotProduct_self_eq_zero.1 (le_antisymm hq (dotProduct_self_nonneg _))
  rw [← hrank]
  exact Matrix.rank_le_card_height _

end NLAlib
