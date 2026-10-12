import NLAlib.Matrix.Factorizations.Cholesky

/-!
# Triangular Cholesky factors for positive-semidefinite matrices

Semidefinite Cholesky existence over every finite linearly ordered index type, transported from
the `Fin n` recursion `cholesky` (`exists_eq_mul_transpose_of_posSemidef`). A vanishing pivot
forces the first row and column to vanish, so the total square-root formula also works at zero
pivots. Source: Higham, Theorem 10.1; Golub--Van Loan, Theorem 4.2.7.
Atlas target: `cholesky-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The semidefinite Cholesky factor exists over every linearly ordered finite
index type; finite normalization preserves the order and all zero pivots. Every PSD real
matrix has a lower-triangular Cholesky factor with nonnegative diagonal, including singular
matrices and the empty matrix. Higham, Theorem 10.1; Golub--Van Loan, Theorem 4.2.7.
atlas: cholesky-decomposition (partial) -/
theorem exists_cholesky_of_posSemidef_fintype {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    ∃ L : Matrix ι ι ℝ, L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧ L * Lᵀ = A := by
  let e : Fin (Fintype.card ι) ≃o ι := monoEquivOfFin ι rfl
  let A' := A.reindex e.symm.toEquiv e.symm.toEquiv
  have hA' : A'.PosSemidef := hA.submatrix e
  obtain ⟨L', hLower, hDiag, hFactor⟩ := exists_eq_mul_transpose_of_posSemidef hA'
  let L := L'.reindex e.toEquiv e.toEquiv
  refine ⟨L, ?_, ?_, ?_⟩
  · intro i j hij
    exact hLower (e.symm.strictMono hij)
  · intro i
    exact hDiag (e.symm i)
  · calc
      L * Lᵀ = (L' * L'ᵀ).reindex e.toEquiv e.toEquiv := by
        simp only [L, Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
      _ = A'.reindex e.toEquiv e.toEquiv := congrArg
        (fun M => M.reindex e.toEquiv e.toEquiv) hFactor.symm
      _ = A := by ext i j; simp [A', Matrix.reindex_apply]

end NLAlib
