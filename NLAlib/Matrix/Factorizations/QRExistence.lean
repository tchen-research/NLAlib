import NLAlib.Matrix.Subspaces.GramIsometry
import NLAlib.Matrix.Factorizations.CholeskyDefinite
import NLAlib.Matrix.Factorizations.QR
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

/-- **Existence of a thin QR with nonnegative diagonal** (`IsQR A Q R`, `R_ii ≥ 0`) for every
real matrix with at least as many rows as columns, on arbitrary finite row indices and ordered
finite column indices; no rank hypothesis, empty dimensions included. Proof: Cholesky of the
Gram matrix `AᵀA` and a range isometry. (A second route, through the full QR
`exists_isFullQR` and `IsFullQR.isQR_castLE`, is constructive via Householder.)
Trefethen--Bau 1997, Thm 7.1; Golub--Van Loan 2013, Thms 5.2.1 and 5.2.3.
atlas: qr-decomposition (partial) -/
theorem exists_isQR (A : Matrix m n ℝ) (hCard : Fintype.card n ≤ Fintype.card m) :
    ∃ Q R, IsQR A Q R ∧ ∀ i, 0 ≤ R i i := by
  classical
  have hGramPSD : (Aᵀ * A).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  obtain ⟨L, hLower, hDiag, hFactor'⟩ := exists_eq_mul_transpose_of_posSemidef hGramPSD
  have hFactor := hFactor'.symm
  let R := Lᵀ
  obtain ⟨J, hJ⟩ := exists_hasOrthonormalCols_of_card_le hCard
  have hJGram : Jᵀ * J = 1 := hJ
  have hGram : Aᵀ * A = (J * R)ᵀ * (J * R) := by
    calc
      Aᵀ * A = Rᵀ * R := by simpa only [R, Matrix.transpose_transpose] using hFactor.symm
      _ = Rᵀ * (Jᵀ * J) * R := by rw [hJGram, Matrix.mul_one]
      _ = (J * R)ᵀ * (J * R) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  obtain ⟨U, hU, hUFactor⟩ := exists_orthogonal_mul_eq_of_gram_eq A (J * R) hGram
  refine ⟨U * J, R, ⟨?_, ?_, hLower.transpose⟩, hDiag⟩
  · simpa only [Matrix.mul_assoc] using hUFactor.symm
  · show (U * J)ᵀ * (U * J) = 1
    have hUGram : Uᵀ * U = 1 := hU
    calc
      (U * J)ᵀ * (U * J) = Jᵀ * (Uᵀ * U) * J := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hUGram, Matrix.mul_one, hJGram]

/-- **Existence with positive diagonal under full column rank**: if `AᵀA` is invertible
(`rank A = |n|`), `A` has a thin QR with `R_ii > 0`. Trefethen–Bau 1997, Thm 7.2;
Golub–Van Loan 2013, Thm 5.2.3. The row-count condition `|n| ≤ |m|` follows from the rank.
atlas: qr-decomposition (partial) -/
theorem exists_isQR_of_isUnit {A : Matrix m n ℝ} (hA : IsUnit (Aᵀ * A)) :
    ∃ Q R, IsQR A Q R ∧ ∀ i, 0 < R i i := by
  have hn : Fintype.card n ≤ Fintype.card m := by
    have h1 := Matrix.rank_of_isUnit _ hA
    rw [Matrix.rank_transpose_mul_self] at h1
    exact h1 ▸ Matrix.rank_le_card_height A
  obtain ⟨Q, R, h, hpos⟩ := exists_isQR A hn
  exact ⟨Q, R, h, fun i => lt_of_le_of_ne (hpos i)
    (h.isUnit_transpose_mul_self_iff.1 hA i).symm⟩

end NLAlib
