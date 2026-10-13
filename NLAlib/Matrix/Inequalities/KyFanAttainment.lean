import NLAlib.Matrix.Inequalities.KyFan
/-!
# Attainment in Ky Fan's maximum and minimum principles

Selecting columns of the spectral basis or of the SVD produces the optimizers,
including at zero and at full dimension. Source: Fan (1949), Theorem 1.
Atlas: `ky-fan-maximum-principle`.
-/

noncomputable section
open scoped Matrix BigOperators

namespace NLAlib

/-- In spectral coordinates, selecting orthogonal columns of a diagonalizing
matrix compresses a matrix to the selected diagonal entries. Ky Fan helper. -/
theorem compression_submatrix_cols_eq_diagonal {n r : Type*} [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r] {A P : Matrix n n ℝ} (hP : HasOrthonormalCols P)
    (d : n → ℝ) (hA : A = P * Matrix.diagonal d * Pᵀ) (e : r ↪ n) :
    (P.submatrix id e)ᵀ * A * P.submatrix id e = Matrix.diagonal (d ∘ e) := by
  have hwhole : Pᵀ * A * P = Matrix.diagonal d := by
    calc
      Pᵀ * A * P = (Pᵀ * P) * Matrix.diagonal d * (Pᵀ * P) := by
        rw [hA]
        simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal d := by rw [(show Pᵀ * P = 1 from hP), Matrix.one_mul, Matrix.mul_one]
  have h1 := Matrix.submatrix_mul_equiv Pᵀ A e (Equiv.refl n) id
  have h2 := Matrix.submatrix_mul_equiv (Pᵀ * A) P e (Equiv.refl n) e
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id] at h1 h2
  rw [Matrix.transpose_submatrix, h1, h2, hwhole,
    Matrix.submatrix_diagonal_embedding]

/-- The top eigenvectors attain the top eigenvalue sum. This supplies an actual
orthonormal optimizing frame for every admissible dimension, also zero.
Fan (1949), Theorem 1.
atlas: ky-fan-maximum-principle (partial) -/
theorem exists_trace_compression_eq_eigenvaluePrefix {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card n) : ∃ Q : Matrix n (Fin k) ℝ,
      HasOrthonormalCols Q ∧ (Qᵀ * A * Q).trace = eigenvaluePrefix hA hk := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let f : Fin k ↪ n := (Fin.castLEEmb hk).trans e.toEmbedding
  let P : Matrix n n ℝ := hA.eigenvectorUnitary
  have hP : HasOrthonormalCols P := transpose_eigenvectorUnitary_mul_self hA
  refine ⟨P.submatrix id f, hP.submatrix_cols f, ?_⟩
  rw [compression_submatrix_cols_eq_diagonal hP hA.eigenvalues
    (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA) f, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.IsHermitian.eigenvalues, f, e]

/-- The bottom eigenvectors attain the bottom eigenvalue sum. Fan (1949), the
minimum principle, including zero and full dimension.
atlas: ky-fan-maximum-principle (partial) -/
theorem exists_trace_compression_eq_bottom_eigenvalues {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card n) : ∃ Q : Matrix n (Fin k) ℝ,
      HasOrthonormalCols Q ∧ (Qᵀ * A * Q).trace =
        ∑ i : Fin k, hA.eigenvalues₀ ⟨i.val + (Fintype.card n - k), by omega⟩ := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let f : Fin k ↪ n := (Fin.natAdd_castLEEmb hk).trans e.toEmbedding
  let P : Matrix n n ℝ := hA.eigenvectorUnitary
  have hP : HasOrthonormalCols P := transpose_eigenvectorUnitary_mul_self hA
  refine ⟨P.submatrix id f, hP.submatrix_cols f, ?_⟩
  rw [compression_submatrix_cols_eq_diagonal hP hA.eigenvalues
    (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA) f, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.IsHermitian.eigenvalues, f, e, Fin.natAdd_castLEEmb]
  congr 1

/-- `Fin` step of `exists_trace_twoSided_compression_eq_kyFanNorm`: the top singular
vectors of an SVD attain the Ky Fan sum. -/
private theorem exists_trace_twoSided_compression_eq_kyFanNorm_fin {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hk : k ≤ min m n) :
    ∃ (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin k) ℝ),
      HasOrthonormalCols U ∧ HasOrthonormalCols V ∧ (Uᵀ * A * V).trace = kyFanNorm A k := by
  obtain ⟨P, R, hSVD⟩ := exists_isSVD A
  let em := Fin.castLEEmb (hk.trans (min_le_left m n))
  let en := Fin.castLEEmb (hk.trans (min_le_right m n))
  have hP : HasOrthonormalCols P := hSVD.transpose_mul_left
  have hR : HasOrthonormalCols R := hSVD.transpose_mul_right
  refine ⟨P.submatrix id em, R.submatrix id en, hP.submatrix_cols em,
    hR.submatrix_cols en, ?_⟩
  have hwhole : Pᵀ * A * R = rectDiag (singularValues A) := by
    calc
      Pᵀ * A * R = (Pᵀ * P) *
          (rectDiag (singularValues A) : Matrix (Fin m) (Fin n) ℝ) * (Rᵀ * R) := by
        conv_lhs => rw [hSVD.eq_mul_transpose]
        simp only [Matrix.mul_assoc]
      _ = rectDiag (singularValues A) := by
          rw [(show Pᵀ * P = 1 from hP), (show Rᵀ * R = 1 from hR), Matrix.one_mul, Matrix.mul_one]
  have h1 := Matrix.submatrix_mul_equiv Pᵀ A em (Equiv.refl (Fin m)) id
  have h2 := Matrix.submatrix_mul_equiv (Pᵀ * A) R em (Equiv.refl (Fin n)) en
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id] at h1 h2
  rw [Matrix.transpose_submatrix, h1, h2, hwhole]
  have hd : (rectDiag (singularValues A) : Matrix (Fin m) (Fin n) ℝ).submatrix em en =
      Matrix.diagonal (fun i : Fin k => singularValues A i.val) := by
    ext i j
    simp only [Matrix.submatrix_apply, rectDiag_apply, Matrix.diagonal_apply,
      em, en, Fin.coe_castLEEmb, Fin.val_castLE]
    simp [Fin.val_inj]
  rw [hd, Matrix.trace_diagonal, kyFanNorm, Fin.sum_univ_eq_sum_range]
  rfl

/-- Actual top singular frames attain the Ky Fan singular-value sum on arbitrary finite
row and column types, for every admissible prefix including zero and full prefixes.
Fan (1949), Theorem 1; Horn–Johnson (1991), Theorem 3.4.1.
atlas: ky-fan-maximum-principle (partial) -/
theorem exists_trace_twoSided_compression_eq_kyFanNorm {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) {k : ℕ}
    (hk : k ≤ min (Fintype.card m) (Fintype.card n)) :
    ∃ (U : Matrix m (Fin k) ℝ) (V : Matrix n (Fin k) ℝ),
      HasOrthonormalCols U ∧ HasOrthonormalCols V ∧ (Uᵀ * A * V).trace = kyFanNorm A k := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let Af := A.reindex em en
  obtain ⟨Uf, Vf, hUf, hVf, ht⟩ := exists_trace_twoSided_compression_eq_kyFanNorm_fin Af hk
  let er := Equiv.refl (Fin k)
  refine ⟨Uf.reindex em.symm er, Vf.reindex en.symm er,
    hUf.reindex em.symm er, hVf.reindex en.symm er, ?_⟩
  have hback : Af.reindex em.symm en.symm = A := by
    ext i j
    simp [Af, Matrix.reindex_apply]
  have h := twoSided_compression_trace_reindex Af Uf Vf em.symm en.symm er
  rw [hback, ht, kyFanNorm_reindex] at h
  exact h

end NLAlib
