import NLAlib.Matrix.Spectral.SingularInterlacing
/-!
# One-row and one-column singular-value deletion

Specialisations of the submatrix interlacing theorems of `SingularInterlacing.lean`
(`singularValues_submatrix_interlacing` and its row/column halves) to deleting one specified
row or column of a `Fin`-indexed matrix.
Source: Horn--Johnson (2013), Corollary 7.3.6.
Atlas: `singular-value-interlacing`.
-/

noncomputable section

namespace NLAlib

/-- Deleting one specified row gives one-step interlacing, including all
end zeros. Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing (partial) -/
theorem singularValues_delete_row_interlacing {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) ℝ) (i : Fin (m + 1)) (k : ℕ) :
    singularValues A (k + 1) ≤ singularValues (A.submatrix i.succAbove id) k ∧
      singularValues (A.submatrix i.succAbove id) k ≤ singularValues A k := by
  have h := singularValues_le_submatrix_rows A i.succAbove Fin.succAbove_right_injective k
  simp only [Fintype.card_fin, Nat.add_sub_cancel_left] at h
  exact ⟨h, singularValues_submatrix_rows_le A i.succAbove Fin.succAbove_right_injective k⟩

/-- Deleting one specified column gives one-step interlacing, including
all end zeros. Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing (partial) -/
theorem singularValues_delete_col_interlacing {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (j : Fin (n + 1)) (k : ℕ) :
    singularValues A (k + 1) ≤ singularValues (A.submatrix id j.succAbove) k ∧
      singularValues (A.submatrix id j.succAbove) k ≤ singularValues A k := by
  have h := singularValues_le_submatrix_cols A j.succAbove Fin.succAbove_right_injective k
  simp only [Fintype.card_fin, Nat.add_sub_cancel_left] at h
  exact ⟨h, singularValues_submatrix_cols_le A j.succAbove Fin.succAbove_right_injective k⟩

end NLAlib
