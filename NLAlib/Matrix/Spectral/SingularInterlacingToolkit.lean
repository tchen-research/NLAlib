import NLAlib.Matrix.Spectral.SingularInterlacing
/-!
# Public singular-value deletion toolkit

The general finite-index native spectral result is exposed in NLAlib's
existing `singularValues` vocabulary for `Fin`-indexed matrices, including
the one-row and one-column deletion chains.
Source: Horn--Johnson (2013), Corollary 7.3.6.
Atlas: `singular-value-interlacing`.
-/

noncomputable section

namespace NLAlib

/-- Row and column deletion gives the full interval for NLAlib's actual
padded singular-value list. Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing -/
theorem singularValues_submatrix_interlacing {m n p q : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (f : Fin p → Fin m) (g : Fin q → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g) (k : ℕ) :
    singularValues A (k + (m - p) + (n - q)) ≤ singularValues (A.submatrix f g) k ∧
      singularValues (A.submatrix f g) k ≤ singularValues A k := by
  simpa only [singularValues_eq_linearMap, Fintype.card_fin] using
    toEuclideanLin_singularValues_submatrix_interlacing A f g hf hg k

/-- Row selection gives both singular-value bounds in the library's public
singular-value vocabulary. Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing (partial) -/
theorem singularValues_submatrix_rows_interlacing {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (f : Fin p → Fin m)
    (hf : Function.Injective f) (k : ℕ) :
    singularValues A (k + (m - p)) ≤ singularValues (A.submatrix f id) k ∧
      singularValues (A.submatrix f id) k ≤ singularValues A k := by
  simpa only [singularValues_eq_linearMap, Fintype.card_fin] using
    And.intro (toEuclideanLin_singularValues_le_submatrix_rows A f hf k)
      (toEuclideanLin_singularValues_submatrix_rows_le A f hf k)

/-- Column selection gives both singular-value bounds in the library's
public singular-value vocabulary. Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing (partial) -/
theorem singularValues_submatrix_cols_interlacing {m n q : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (g : Fin q → Fin n)
    (hg : Function.Injective g) (k : ℕ) :
    singularValues A (k + (n - q)) ≤ singularValues (A.submatrix id g) k ∧
      singularValues (A.submatrix id g) k ≤ singularValues A k := by
  simpa only [singularValues_eq_linearMap, Fintype.card_fin] using
    And.intro (toEuclideanLin_singularValues_le_submatrix_cols A g hg k)
      (toEuclideanLin_singularValues_submatrix_cols_le A g hg k)

/-- Deleting one specified row gives one-step interlacing, including all
end zeros. Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing (partial) -/
theorem singularValues_delete_row_interlacing {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) ℝ) (i : Fin (m + 1)) (k : ℕ) :
    singularValues A (k + 1) ≤ singularValues (A.submatrix i.succAbove id) k ∧
      singularValues (A.submatrix i.succAbove id) k ≤ singularValues A k := by
  simpa only [Nat.add_sub_cancel_left] using
    singularValues_submatrix_rows_interlacing A i.succAbove (Fin.succAbove_right_injective) k

/-- Deleting one specified column gives one-step interlacing, including
all end zeros. Horn--Johnson (2013), Corollary 7.3.6.
atlas: singular-value-interlacing (partial) -/
theorem singularValues_delete_col_interlacing {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (j : Fin (n + 1)) (k : ℕ) :
    singularValues A (k + 1) ≤ singularValues (A.submatrix id j.succAbove) k ∧
      singularValues (A.submatrix id j.succAbove) k ≤ singularValues A k := by
  simpa only [Nat.add_sub_cancel_left] using
    singularValues_submatrix_cols_interlacing A j.succAbove (Fin.succAbove_right_injective) k

end NLAlib
