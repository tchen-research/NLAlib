import NLAlib.Matrix.NearestPolar

/-!
# Complete real polar-decomposition contract

The tall, wide and square factorizations, positive-factor uniqueness,
full-rank equivalence for isometry uniqueness and nearest-isometry theorem
in every invariant norm are assembled without missing rank or endpoint cases.
-/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib

/-- All real polar-decomposition clauses, including arbitrary rank, empty
indices, wide coisometries, exact uniqueness conditions and minimization in
every invariant norm. Horn–Johnson 2013, Theorem 7.3.1; source re-derivation
§`alg:polar`. A minimizer's uniqueness for every norm is not asserted.
atlas: polar-decomposition -/
theorem polar_decomposition_properties {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    (Fintype.card n ≤ Fintype.card m →
      ∃ U : Matrix m n ℝ, HasOrthonormalCols U ∧ U * CFC.sqrt (Aᵀ * A) = A ∧
        ((∀ V : Matrix m n ℝ, HasOrthonormalCols V →
          V * CFC.sqrt (Aᵀ * A) = A → V = U) ↔ A.rank = Fintype.card n) ∧
        (A.rank = Fintype.card n → U = polarFrame A) ∧
        (∀ (ν : OrthogonallyInvariantNorm m n) (V : Matrix m n ℝ),
          HasOrthonormalCols V → ν.seminorm (A - U) ≤ ν.seminorm (A - V))) ∧
    (Fintype.card m ≤ Fintype.card n →
      ∃ U : Matrix m n ℝ, U * Uᵀ = 1 ∧ CFC.sqrt (A * Aᵀ) * U = A ∧
        ((∀ V : Matrix m n ℝ, V * Vᵀ = 1 →
          CFC.sqrt (A * Aᵀ) * V = A → V = U) ↔ A.rank = Fintype.card m) ∧
        (∀ (ν : OrthogonallyInvariantNorm m n) (V : Matrix m n ℝ),
          V * Vᵀ = 1 → ν.seminorm (A - U) ≤ ν.seminorm (A - V))) ∧
    (∀ (U : Matrix m n ℝ) (Q : Matrix n n ℝ), HasOrthonormalCols U →
      Q.PosSemidef → U * Q = A → Q = CFC.sqrt (Aᵀ * A)) ∧
    (∀ B : Matrix n n ℝ, ∃ U : Matrix n n ℝ, HasOrthonormalCols U ∧
      U * CFC.sqrt (Bᵀ * B) = B ∧ CFC.sqrt (B * Bᵀ) * U = B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hCard
    obtain ⟨U, hU, hA⟩ := exists_isometry_mul_sqrt_gram_eq A hCard
    exact ⟨U, hU, hA, polar_isometry_unique_iff_rank_eq_card hU hA,
      fun hRank => eq_polarFrame_of_isometry_mul_sqrt_gram_eq hRank hA,
      fun ν V hV => invariantNorm_sub_polar_le_sub_isometry ν A U V hCard hU hA hV⟩
  · intro hCard
    obtain ⟨U, hU, hA⟩ := exists_sqrt_rowGram_mul_coisometry_eq A hCard
    exact ⟨U, hU, hA, polar_coisometry_unique_iff_rank_eq_card hU hA,
      fun ν V hV => invariantNorm_sub_polar_le_sub_coisometry ν A U V hCard hU hA hV⟩
  · intro U Q hU hQ hA
    exact eq_sqrt_gram_of_isometry_mul_eq hU hQ hA
  · intro B
    obtain ⟨U, hU, hB⟩ := exists_isometry_mul_sqrt_gram_eq B le_rfl
    exact ⟨U, hU, hB, sqrt_rowGram_mul_eq_of_isometry_mul_sqrt_gram_eq hU hB⟩

end NLAlib
