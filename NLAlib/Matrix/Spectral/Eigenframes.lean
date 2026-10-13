import NLAlib.Matrix.Inequalities.KyFanAttainment
/-!
# Sorted spectral frames

Named top and complementary eigenframes expose the actual spectral bases used
in the Ky Fan variational optimizers and in gap-based projector comparisons.
Source: Horn–Johnson (2013), §4.3.
-/

noncomputable section
open scoped Matrix BigOperators

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- The matrix of all eigenvectors in decreasing eigenvalue order. -/
def sortedEigenframe (hA : A.IsHermitian) : Matrix n (Fin (Fintype.card n)) ℝ :=
  (hA.eigenvectorUnitary : Matrix n n ℝ).submatrix id
    (Fintype.equivOfCardEq (Fintype.card_fin _))

/-- The sorted spectral frame has orthonormal columns. -/
theorem hasOrthonormalCols_sortedEigenframe (hA : A.IsHermitian) :
    HasOrthonormalCols (sortedEigenframe hA) :=
  (show HasOrthonormalCols (hA.eigenvectorUnitary : Matrix n n ℝ) from
    transpose_eigenvectorUnitary_mul_self hA).submatrix_cols
      (Fintype.equivOfCardEq (Fintype.card_fin _)).toEmbedding

/-- The sorted spectral frame diagonalizes the matrix with decreasing eigenvalues. -/
theorem compression_sortedEigenframe_eq_diagonal (hA : A.IsHermitian) :
    (sortedEigenframe hA)ᵀ * A * sortedEigenframe hA = Matrix.diagonal hA.eigenvalues₀ := by
  have h := compression_submatrix_cols_eq_diagonal
    (show HasOrthonormalCols (hA.eigenvectorUnitary : Matrix n n ℝ) from
      transpose_eigenvectorUnitary_mul_self hA) hA.eigenvalues
    (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA)
    (Fintype.equivOfCardEq (Fintype.card_fin _)).toEmbedding
  simpa [sortedEigenframe, Matrix.IsHermitian.eigenvalues, Function.comp_def] using h

/-- The first `k` columns of the sorted spectral frame. -/
def topEigenframe (hA : A.IsHermitian) {k : ℕ} (hk : k ≤ Fintype.card n) : Matrix n (Fin k) ℝ :=
  (sortedEigenframe hA).submatrix id (Fin.castLEEmb hk)

/-- The complementary final `card n - k` columns of the sorted spectral frame. -/
def complementaryEigenframe (hA : A.IsHermitian) {k : ℕ} (_hk : k ≤ Fintype.card n) :
    Matrix n (Fin (Fintype.card n - k)) ℝ :=
  (sortedEigenframe hA).submatrix id
    (Fin.natAdd_castLEEmb (Nat.sub_le (Fintype.card n) k))

/-- Top eigenframes have orthonormal columns, at every admissible dimension. -/
theorem hasOrthonormalCols_topEigenframe (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card n) : HasOrthonormalCols (topEigenframe hA hk) :=
  (hasOrthonormalCols_sortedEigenframe hA).submatrix_cols (Fin.castLEEmb hk)

/-- Complementary eigenframes have orthonormal columns. -/
theorem hasOrthonormalCols_complementaryEigenframe (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card n) : HasOrthonormalCols (complementaryEigenframe hA hk) :=
  (hasOrthonormalCols_sortedEigenframe hA).submatrix_cols
    (Fin.natAdd_castLEEmb (Nat.sub_le (Fintype.card n) k))

/-- The top-frame compression is diagonal with exactly the first `k` eigenvalues. -/
theorem compression_topEigenframe_eq_diagonal (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card n) :
    (topEigenframe hA hk)ᵀ * A * topEigenframe hA hk =
      Matrix.diagonal (fun i : Fin k => hA.eigenvalues₀ (Fin.castLE hk i)) := by
  have h1 := Matrix.submatrix_mul_equiv (sortedEigenframe hA)ᵀ A
    (Fin.castLEEmb hk) (Equiv.refl n) id
  have h2 := Matrix.submatrix_mul_equiv ((sortedEigenframe hA)ᵀ * A) (sortedEigenframe hA)
    (Fin.castLEEmb hk) (Equiv.refl n) (Fin.castLEEmb hk)
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id] at h1 h2
  rw [topEigenframe, Matrix.transpose_submatrix, h1, h2,
    compression_sortedEigenframe_eq_diagonal, Matrix.submatrix_diagonal_embedding]
  rfl

/-- The complementary compression is diagonal with exactly the eigenvalues
following the top `k`; no zero or simple-spectrum assumption is imposed. -/
theorem compression_complementaryEigenframe_eq_diagonal (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card n) :
    (complementaryEigenframe hA hk)ᵀ * A * complementaryEigenframe hA hk =
      Matrix.diagonal (fun i : Fin (Fintype.card n - k) =>
        hA.eigenvalues₀ ⟨i.val + k, by omega⟩) := by
  let e := Fin.natAdd_castLEEmb (Nat.sub_le (Fintype.card n) k)
  have h1 := Matrix.submatrix_mul_equiv (sortedEigenframe hA)ᵀ A e (Equiv.refl n) id
  have h2 := Matrix.submatrix_mul_equiv ((sortedEigenframe hA)ᵀ * A) (sortedEigenframe hA)
    e (Equiv.refl n) e
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id] at h1 h2
  rw [complementaryEigenframe, Matrix.transpose_submatrix, h1, h2,
    compression_sortedEigenframe_eq_diagonal, Matrix.submatrix_diagonal_embedding]
  congr 1
  funext i
  change hA.eigenvalues₀ (e i) = hA.eigenvalues₀ ⟨i.val + k, by omega⟩
  apply congrArg hA.eigenvalues₀
  apply Fin.ext
  simp [e, Fin.natAdd_castLEEmb, Nat.sub_sub_self hk]

end NLAlib
