import NLAlib.Matrix.Basic.ComplementaryNullities
/-!
# Explicit rank form of complementary right nullities

Right nullity is column cardinality minus rank. Horn–Johnson 2013,
§§0.7.5–0.7.6; atlas `complementary-nullities`, `cs-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Complementary nullities give the explicit rectangular column-cardinality
minus rank identity. Row cardinalities are deliberately not used as nullity.
Holds over any field (generalised from `ℝ`, covering `ℂ`). Horn–Johnson 2013,
§§0.7.5–0.7.6.
atlas: complementary-nullities (partial), cs-decomposition (partial) -/
theorem card_columns_sub_rank_toBlock_eq_inverse_complement {n : Type*}
    [Fintype n] [DecidableEq n] {K : Type*} [Field K] (A : Matrix n n K) (hA : IsUnit A.det)
    (p q : n → Prop) [DecidablePred p] [DecidablePred q] :
    Fintype.card {j // q j} - (A.toBlock p q).rank =
      Fintype.card {j // ¬p j} - (A⁻¹.toBlock (fun i => ¬q i) (fun i => ¬p i)).rank := by
  have hA₁ := (A.toBlock p q).mulVecLin.finrank_range_add_finrank_ker
  have hA₂ := (A⁻¹.toBlock (fun i => ¬q i) (fun i => ¬p i)).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hA₁ hA₂
  have h := finrank_ker_toBlock_eq_finrank_ker_inverse_complement A hA p q
  change (A.toBlock p q).rank + _ = _ at hA₁
  change (A⁻¹.toBlock (fun i => ¬q i) (fun i => ¬p i)).rank + _ = _ at hA₂
  omega

end NLAlib
