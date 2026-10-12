import NLAlib.Matrix.Factorizations.CholeskyDefinite
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Hadamard's determinant bound and equality

The triangular Gram factor gives the determinant as a product of diagonal
squares, each bounded by its full row energy. Positive definite equality
forces the factor and the matrix to be diagonal. The singular PSD equality
case additionally allows a zero diagonal entry.
Source: Horn--Johnson (2013), Theorem 7.8.1; atlas `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The diagonal square of a square Gram factor is bounded by its row
energy, the corresponding diagonal entry of the Gram matrix.
Horn--Johnson (2013), proof of Theorem 7.8.1; helper for Hadamard's bound. -/
theorem sq_diag_le_gram_diag (L : Matrix n n ℝ) (i : n) :
    L i i ^ 2 ≤ (L * Lᵀ) i i := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ← sq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (L i j)) (Finset.mem_univ i)

/-- Hadamard's inequality on the full PSD cone, with arbitrary finite
coordinate types and the empty determinant convention.
Horn--Johnson (2013), Theorem 7.8.1 and its semidefinite extension.
atlas: hadamard-fischer-inequalities (partial) -/
theorem det_le_prod_diag_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.det ≤ ∏ i, A i i := by
  classical
  let O := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  let : LinearOrder n := { O with
    toDecidableEq := ‹DecidableEq n›
    compare_eq_compareOfLessAndEq := by
      intro a b
      have he : O.toDecidableEq = ‹DecidableEq n› := Subsingleton.elim _ _
      change @compare n O.toOrd a b =
        @compareOfLessAndEq n a b O.toLT (O.toDecidableLT a b) ‹DecidableEq n›
      rw [← he]
      exact @LinearOrder.compare_eq_compareOfLessAndEq n O a b }
  obtain ⟨L, hL, -, hLA⟩ := exists_cholesky_of_posSemidef_fintype A hA
  rw [det_eq_prod_sq_diag_of_cholesky A L hL hLA]
  apply Finset.prod_le_prod (fun i _ => sq_nonneg (L i i))
  intro i _
  simpa only [hLA] using sq_diag_le_gram_diag L i

/-- Equality in positive definite Hadamard holds exactly for a diagonal
matrix. Horn--Johnson (2013), Theorem 7.8.1.
atlas: hadamard-fischer-inequalities (partial) -/
theorem det_eq_prod_diag_iff_isDiag_of_posDef {A : Matrix n n ℝ} (hA : A.PosDef) :
    A.det = (∏ i, A i i) ↔ A.IsDiag := by
  classical
  constructor
  · intro hdet
    let O := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
    let : LinearOrder n := { O with
      toDecidableEq := ‹DecidableEq n›
      compare_eq_compareOfLessAndEq := by
        intro a b
        have he : O.toDecidableEq = ‹DecidableEq n› := Subsingleton.elim _ _
        change @compare n O.toOrd a b =
          @compareOfLessAndEq n a b O.toLT (O.toDecidableLT a b) ‹DecidableEq n›
        rw [← he]
        exact @LinearOrder.compare_eq_compareOfLessAndEq n O a b }
    obtain ⟨L, ⟨hLower, hPos, hLA⟩, -⟩ := existsUnique_cholesky_of_posDef A hA
    have hle (i : n) : L i i ^ 2 ≤ A i i := by
      simpa only [hLA] using sq_diag_le_gram_diag L i
    have heq (i : n) : L i i ^ 2 = A i i := by
      by_contra hne
      have hi : L i i ^ 2 < A i i := lt_of_le_of_ne (hle i) hne
      have hp := Finset.prod_lt_prod (s := (Finset.univ : Finset n))
        (fun j _ => sq_pos_of_pos (hPos j)) (fun j _ => hle j) ⟨i, Finset.mem_univ i, hi⟩
      rw [← det_eq_prod_sq_diag_of_cholesky A L hLower hLA, hdet] at hp
      exact (lt_irrefl _ hp)
    have hLDiag : L.IsDiag := by
      intro i j hij
      have hrow : (∑ k, L i k ^ 2) = L i i ^ 2 := by
        rw [heq, ← hLA, Matrix.mul_apply]
        simp only [Matrix.transpose_apply, sq]
      have hrest : ∑ k ∈ Finset.univ.erase i, L i k ^ 2 = 0 := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hrow
        linarith
      have hj0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => sq_nonneg (L i k))).mp hrest j (by simp [hij.symm])
      exact sq_eq_zero_iff.mp hj0
    rw [← hLA, ← hLDiag.diagonal_diag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    exact Matrix.isDiag_diagonal _
  · intro hDiag
    calc
      A.det = (diagonal A.diag).det := congrArg Matrix.det hDiag.diagonal_diag.symm
      _ = ∏ i, A i i := by rw [Matrix.det_diagonal]; rfl

/-- PSD Hadamard equality holds exactly for a diagonal matrix or a zero
diagonal entry. The latter forces a zero row and column and both products
to vanish. Horn--Johnson (2013), Theorem 7.8.1; explicit singular equality
extension supporting the column-determinant bound.
atlas: hadamard-fischer-inequalities (partial) -/
theorem det_eq_prod_diag_iff_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.det = (∏ i, A i i) ↔ A.IsDiag ∨ ∃ i, A i i = 0 := by
  constructor
  · intro heq
    by_cases hz : ∃ i, A i i = 0
    · exact Or.inr hz
    · have hpos (i : n) : 0 < A i i := lt_of_le_of_ne hA.diag_nonneg
        (Ne.symm (fun hi => hz ⟨i, hi⟩))
      have hd : 0 < A.det := by rw [heq]; exact Finset.prod_pos (fun i _ => hpos i)
      have hPD := hA.posDef_iff_det_ne_zero.mpr hd.ne'
      exact Or.inl ((det_eq_prod_diag_iff_isDiag_of_posDef hPD).mp heq)
  · rintro (hDiag | ⟨i, hi⟩)
    · calc
        A.det = (diagonal A.diag).det := congrArg Matrix.det hDiag.diagonal_diag.symm
        _ = ∏ j, A j j := by rw [Matrix.det_diagonal]; rfl
    · have hp : ∏ j, A j j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
      have hle := det_le_prod_diag_of_posSemidef hA
      rw [hp] at hle ⊢
      exact le_antisymm hle hA.det_nonneg

end NLAlib
