import NLAlib.Matrix.Factorizations.QRCompletion
import NLAlib.Matrix.Factorizations.QRConsequences
/-!
# Complete thin and full QR contract

Thin and full existence, a nonnegative triangular corner, uniqueness at
full column rank, the actual range projector, and preservation of the
native singular spectrum and spectral condition number. Source:
Trefethen--Bau, Theorems 7.1--7.2; Golub--Van Loan, Theorems 5.2.1 and 5.2.3.
Atlas: `qr-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Complete QR factorization for real matrices with at least as many rows
as columns. The thin factor has nonnegative upper diagonal and the actual
Gram, native singular values and Moore--Penrose condition number of the
input. For every coordinate embedding the same frame and triangular factor
extend to a full orthogonal factorization with a zero-padded corner. At full
column rank the diagonal is positive, the actual range projector agrees
with the Moore--Penrose projector, and the pair is unique among positive
diagonal QR pairs. Arbitrary finite row indices, ordered finite column
indices, singular inputs and empty spaces are covered.
Trefethen--Bau, Theorems 7.1--7.2; Golub--Van Loan, Theorems 5.2.1 and 5.2.3.
atlas: qr-decomposition -/
theorem qr_decomposition {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [LinearOrder n] (A : Matrix m n ℝ)
    (hCard : Fintype.card n ≤ Fintype.card m) :
    ∃ Q : Matrix m n ℝ, ∃ R : Matrix n n ℝ,
      HasOrthonormalCols Q ∧ R.IsUpperTriangular ∧ (∀ i, 0 ≤ R i i) ∧ Q * R = A ∧
        Rᵀ * R = Aᵀ * A ∧
        (∀ k, R.toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k) ∧
        conditionNumber R = conditionNumber A ∧
        (∀ e : n ↪ m, ∃ W : Matrix m m ℝ, ∃ T : Matrix m n ℝ,
          HasOrthonormalCols W ∧ W * Wᵀ = 1 ∧ W.submatrix id e = Q ∧
            W * T = A ∧ T.submatrix e id = R ∧
              (∀ i ∉ Set.range e, ∀ j, T i j = 0)) ∧
        (A.rank = Fintype.card n → (∀ i, 0 < R i i) ∧
          Q * Qᵀ = A * moorePenroseInverse A ∧
          ∀ (Q' : Matrix m n ℝ) (R' : Matrix n n ℝ),
            HasOrthonormalCols Q' → R'.IsUpperTriangular →
              (∀ i, 0 < R' i i) → Q' * R' = A → Q' = Q ∧ R' = R) := by
  obtain ⟨Q, R, hQ, hUpper, hDiag, hFactor⟩ := exists_qr A hCard
  refine ⟨Q, R, hQ, hUpper, hDiag, hFactor,
    transpose_mul_self_eq_of_qr hQ hFactor,
    toEuclideanLin_singularValues_eq_of_qr hQ hFactor,
    conditionNumber_eq_of_qr hQ hFactor, ?_, ?_⟩
  · intro e
    obtain ⟨W, T, hW, hCols, hFullFactor, hCorner, hZero⟩ :=
      exists_full_qr_completion hQ hFactor e
    exact ⟨W, T, hW, mul_eq_one_comm.mp hW, hCols, hFullFactor, hCorner, hZero⟩
  · intro hRank
    have hPositive := diag_pos_of_qr_of_rank_eq_card hQ hUpper hDiag hFactor hRank
    refine ⟨hPositive,
      mul_transpose_eq_mul_moorePenroseInverse_of_qr_of_rank_eq_card hQ hFactor hRank, ?_⟩
    intro Q' R' hQ' hUpper' hDiag' hFactor'
    exact qr_pair_unique hRank hQ' hQ hUpper' hUpper hDiag' hPositive hFactor' hFactor

end NLAlib
