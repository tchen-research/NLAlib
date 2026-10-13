import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Rank of a triangular positive prefix

A lower triangular real factor with positive prefix diagonal and zero trailing columns has
rank equal to that prefix length. Source: matrix toolkit rederivations, `lem:rankL`.
-/

noncomputable section

open Matrix Finset

namespace Matrix

/-- The rank of a lower triangular factor with positive prefix and zero column tail is
exactly its prefix length, including the empty prefix.
Source: matrix toolkit rederivations, `lem:rankL`. -/
theorem rank_eq_of_lowerTriangular_positive_prefix {n r : ℕ} (hr : r ≤ n)
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : L.IsLowerTriangular)
    (hpos : ∀ i : Fin n, i.val < r → 0 < L i i)
    (hzero : ∀ i j : Fin n, r ≤ j.val → L i j = 0) : L.rank = r := by
  let e : Fin r → Fin n := Fin.castLE hr
  let B : Matrix (Fin n) (Fin r) ℝ := L.submatrix id e
  let E : Matrix (Fin r) (Fin n) ℝ := fun j k => if k.val = j.val then 1 else 0
  have hfactor : B * E = L := by
    ext i k
    rw [Matrix.mul_apply]
    by_cases hk : k.val < r
    · let j : Fin r := ⟨k.val, hk⟩
      rw [Finset.sum_eq_single j]
      · simp only [B, E, Matrix.submatrix_apply, id_eq, j, ite_true, mul_one]
        exact congrArg (L i) (Fin.ext rfl)
      · intro a ha haj
        have hne : k.val ≠ a.val := fun h => haj (Fin.ext h.symm)
        simp only [E, if_neg hne, mul_zero]
      · simp
    · have hz := hzero i k (by omega)
      rw [hz]
      apply sum_eq_zero
      intro j hj
      have hne : k.val ≠ j.val := by have := j.isLt; omega
      simp only [E, if_neg hne, mul_zero]
  have hupper : L.rank ≤ r := by
    rw [← hfactor]
    exact (Matrix.rank_mul_le_left B E).trans (by simpa only [Fintype.card_fin] using Matrix.rank_le_card_width B)
  let M : Matrix (Fin r) (Fin r) ℝ := L.submatrix e e
  have hMlower : M.IsLowerTriangular := fun i j hij => hL (i := e i) (j := e j) hij
  have hMdet : 0 < M.det := by
    rw [Matrix.det_of_isLowerTriangular M hMlower]
    exact prod_pos fun j hj => hpos (e j) j.isLt
  have hMrank : M.rank = r := by simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hMdet.ne'
  have hlower : r ≤ L.rank := by rw [← hMrank]; exact Matrix.rank_submatrix_le L e e
  exact le_antisymm hupper hlower

end Matrix
