import NLAlib.Matrix.Inequalities.KyFanFiniteIndex
/-!
# Ky Fan singular trace principles on arbitrary finite indices

The real finite SVD core is transported to arbitrary finite row and column
labels. Universal trace bounds and actual optimizers use the original matrix
space, including empty shapes. Source: Fan (1949), Theorem 1.
Atlas: `ky-fan-maximum-principle`.
-/

noncomputable section
open scoped Matrix BigOperators

namespace NLAlib

/-- Simultaneously relabeling both frame spaces and the matrix preserves the
actual two-sided compression trace. -/
theorem twoSided_compression_trace_reindex {m n r p q s : Type*}
    [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q] [Fintype s]
    (A : Matrix m n ℝ) (U : Matrix m r ℝ) (V : Matrix n r ℝ)
    (em : m ≃ p) (en : n ≃ q) (er : r ≃ s) :
    ((U.reindex em er)ᵀ * A.reindex em en * V.reindex en er).trace = (Uᵀ * A * V).trace := by
  have h1 : (U.reindex em er)ᵀ * A.reindex em en = (Uᵀ * A).reindex er en := by
    simpa only [Matrix.reindex_apply, Matrix.transpose_submatrix] using
      Matrix.submatrix_mul_equiv Uᵀ A er.symm em.symm en.symm
  have h2 : (Uᵀ * A).reindex er en * V.reindex en er = (Uᵀ * A * V).reindex er er := by
    simpa only [Matrix.reindex_apply] using
      Matrix.submatrix_mul_equiv (Uᵀ * A) V er.symm en.symm er.symm
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact er.symm.sum_comp (fun i => (Uᵀ * A * V) i i)

/-- Every two-sided orthonormal compression trace is at most its Ky Fan sum,
on arbitrary finite row and frame indices. No dimension hypothesis beyond the
actual orthonormal frames is needed. Fan (1949), Theorem 1.
atlas: ky-fan-maximum-principle (partial) -/
theorem trace_twoSided_compression_le_kyFanNorm_fintype {m n r : Type*}
    [Fintype m] [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    (A : Matrix m n ℝ) {U : Matrix m r ℝ} {V : Matrix n r ℝ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    (Uᵀ * A * V).trace ≤ kyFanNorm A (Fintype.card r) := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let er := Fintype.equivFin r
  have h := trace_twoSided_compression_le_kyFanNorm (A.reindex em en)
    (hU.reindex em er) (hV.reindex en er)
  rwa [twoSided_compression_trace_reindex, kyFanNorm_reindex] at h

/-- Actual top singular frames attain the Ky Fan sum on arbitrary finite
matrix row/column types for every admissible prefix, including zero.
Fan (1949), Theorem 1.
atlas: ky-fan-maximum-principle (partial) -/
theorem exists_trace_twoSided_compression_eq_kyFanNorm_fintype {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) {k : ℕ}
    (hk : k ≤ min (Fintype.card m) (Fintype.card n)) :
    ∃ (U : Matrix m (Fin k) ℝ) (V : Matrix n (Fin k) ℝ),
      HasOrthonormalCols U ∧ HasOrthonormalCols V ∧ (Uᵀ * A * V).trace = kyFanNorm A k := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let Af := A.reindex em en
  obtain ⟨Uf, Vf, hUf, hVf, ht⟩ := exists_trace_twoSided_compression_eq_kyFanNorm Af hk
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
