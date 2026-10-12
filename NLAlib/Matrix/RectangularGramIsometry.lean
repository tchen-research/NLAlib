import NLAlib.Matrix.GramIsometry

/-!
# Rectangular isometries from equality of Gram matrices

Equality of Gram matrices is equivalent to transport by a matrix with
orthonormal columns when the destination has at least the source dimension.
This completes the real rectangular statement of `gram-equality-isometry`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- Equal real Gram matrices admit a rectangular isometry from the smaller
ambient row space to the larger one, including empty and deficient-rank cases.
Horn–Johnson 2013, Theorem 7.3.11; frontier derivations, §`alg:gram-isometry`.
atlas: gram-equality-isometry -/
theorem exists_isometry_mul_eq_of_gram_eq (A : Matrix m n ℝ) (B : Matrix p n ℝ)
    (hCard : Fintype.card m ≤ Fintype.card p) (hGram : Aᵀ * A = Bᵀ * B) :
    ∃ V : Matrix p m ℝ, HasOrthonormalCols V ∧ V * A = B := by
  obtain ⟨J, hJ⟩ := exists_hasOrthonormalCols_of_card_le hCard
  have hPad : Bᵀ * B = (J * A)ᵀ * (J * A) := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᵀ J A,
      hJ, Matrix.one_mul]
    exact hGram.symm
  obtain ⟨O, hO, hEq⟩ := exists_orthogonal_mul_eq_of_gram_eq B (J * A) hPad
  refine ⟨O * J, ?_, ?_⟩
  · change (O * J)ᵀ * (O * J) = 1
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Oᵀ O J,
      hO, Matrix.one_mul, hJ]
  · simpa only [Matrix.mul_assoc] using hEq

/-- A rectangular isometry transporting one matrix to another preserves its
Gram matrix. Together with the existence theorem this gives both directions.
Horn–Johnson 2013, Theorem 7.3.11; frontier derivations, §`alg:gram-isometry`.
atlas: gram-equality-isometry -/
theorem gram_eq_iff_exists_isometry_mul_eq (A : Matrix m n ℝ) (B : Matrix p n ℝ)
    (hCard : Fintype.card m ≤ Fintype.card p) :
    Aᵀ * A = Bᵀ * B ↔
      ∃ V : Matrix p m ℝ, HasOrthonormalCols V ∧ V * A = B := by
  constructor
  · exact exists_isometry_mul_eq_of_gram_eq A B hCard
  · rintro ⟨V, hV, rfl⟩
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V A,
      hV, Matrix.one_mul]

end NLAlib
