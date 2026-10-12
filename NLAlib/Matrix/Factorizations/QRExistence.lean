import NLAlib.Matrix.Subspaces.GramIsometry
import NLAlib.Matrix.Factorizations.CholeskyDefinite
/-!
# QR existence through Cholesky and a range isometry

Every rectangular real matrix with at least as many rows as columns admits
thin QR, including singular matrices and empty dimensions. The triangular
factor comes from Cholesky of the Gram; its range isometry is extended in
the ambient row space. Source: Trefethen--Bau, Theorems 7.1--7.2;
Golub--Van Loan, Theorems 5.2.1 and 5.2.3. Atlas: `qr-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [LinearOrder n]

/-- Thin QR exists with a nonnegative upper-triangular factor on arbitrary
finite row indices and ordered finite column indices. Singular matrices and
empty dimensions are included. Trefethen--Bau, Theorem 7.1;
Golub--Van Loan, Theorem 5.2.1.
atlas: qr-decomposition (partial) -/
theorem exists_qr (A : Matrix m n ℝ) (hCard : Fintype.card n ≤ Fintype.card m) :
    ∃ Q : Matrix m n ℝ, ∃ R : Matrix n n ℝ,
      HasOrthonormalCols Q ∧ R.IsUpperTriangular ∧ (∀ i, 0 ≤ R i i) ∧ Q * R = A := by
  classical
  have hGramPSD : (Aᵀ * A).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  obtain ⟨L, hLower, hDiag, hFactor⟩ :=
    exists_cholesky_of_posSemidef_fintype (Aᵀ * A) hGramPSD
  let R := Lᵀ
  obtain ⟨J, hJ⟩ := exists_hasOrthonormalCols_of_card_le hCard
  have hJGram : Jᵀ * J = 1 := hJ
  have hGram : Aᵀ * A = (J * R)ᵀ * (J * R) := by
    calc
      Aᵀ * A = Rᵀ * R := by simpa only [R, Matrix.transpose_transpose] using hFactor.symm
      _ = Rᵀ * (Jᵀ * J) * R := by rw [hJGram, Matrix.mul_one]
      _ = (J * R)ᵀ * (J * R) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  obtain ⟨U, hU, hUFactor⟩ := exists_orthogonal_mul_eq_of_gram_eq A (J * R) hGram
  refine ⟨U * J, R, ?_, hLower.transpose, hDiag, ?_⟩
  · show (U * J)ᵀ * (U * J) = 1
    have hUGram : Uᵀ * U = 1 := hU
    calc
      (U * J)ᵀ * (U * J) = Jᵀ * (Uᵀ * U) * J := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hUGram, Matrix.mul_one, hJGram]
  · simpa only [Matrix.mul_assoc] using hUFactor

end NLAlib
