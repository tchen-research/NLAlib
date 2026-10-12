import NLAlib.Matrix.Factorizations.CholeskyCharacterization
/-!
# Complete triangular Cholesky decomposition

Semidefinite existence, definite uniqueness, determinant and pivot/trailing
identities are included, with arbitrary finite linearly ordered indices and
explicit empty/zero-pivot behavior. Sources: Higham, Theorem 10.1;
Trefethen--Bau, Theorem 23.1; Golub--Van Loan, Theorem 4.2.7.
Atlas: `cholesky-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Complete Cholesky contract: the PSD existence and PD uniqueness statements,
the determinant identity, and the exact first/trailing pivot characterizations.
No uniqueness is claimed for deficient semidefinite matrices.
Higham, Theorem 10.1; Golub--Van Loan, Theorem 4.2.7.
atlas: cholesky-decomposition -/
theorem cholesky_decomposition {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) :
    (A.PosSemidef → ∃ L : Matrix ι ι ℝ,
      L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧ L * Lᵀ = A) ∧
    (A.PosDef → ∃! L : Matrix ι ι ℝ,
      L.IsLowerTriangular ∧ (∀ i, 0 < L i i) ∧ L * Lᵀ = A) ∧
    (∀ L : Matrix ι ι ℝ, L.IsLowerTriangular → L * Lᵀ = A → A.det = ∏ i, L i i ^ 2) ∧
    (∀ n : ℕ, ∀ B L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      L.IsLowerTriangular → (∀ i, 0 < L i i) → L * Lᵀ = B →
        L 0 0 = Real.sqrt (B 0 0) ∧
        L.submatrix Fin.succ Fin.succ * (L.submatrix Fin.succ Fin.succ)ᵀ =
          choleskyTrailingResidual B) := by
  refine ⟨fun hA => exists_cholesky_of_posSemidef_fintype A hA,
    fun hA => existsUnique_cholesky_of_posDef A hA,
    fun L hLower hFactor => det_eq_prod_sq_diag_of_cholesky A L hLower hFactor, ?_⟩
  intro n B L hLower hDiag hFactor
  exact ⟨cholesky_first_diag_eq_sqrt B L hLower (hDiag 0).le hFactor,
    cholesky_trailing_mul_transpose B L hLower (hDiag 0) hFactor⟩

end NLAlib
