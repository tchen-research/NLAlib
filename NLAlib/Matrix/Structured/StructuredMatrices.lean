import NLAlib.Matrix.Basic.SchurComplement
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Toeplitz, Hankel, Cauchy and Hilbert matrices

Toeplitz uses ordinary integer differences and Hankel ordinary natural sums.
Cauchy determinants follow by Schur elimination with only denominator
nonvanishing; repeated parameters are allowed. Horn–Johnson §§0.9.7–0.9.12.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Toeplitz entries use ordinary integer differences, not modular index
arithmetic. Horn–Johnson 2013, §0.9.7.
atlas: structured-matrices-def (partial) -/
def toeplitzMatrix {m n : ℕ} (t : ℤ → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => t ((j.val : ℤ) - (i.val : ℤ))

/-- Hankel entries use ordinary natural-number sums. Horn–Johnson 2013,
§0.9.8.
atlas: structured-matrices-def (partial) -/
def hankelMatrix {m n : ℕ} (h : ℕ → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => h (i.val + j.val)

/-- A Cauchy matrix has entries `1/(x_i+y_j)`. Its determinant theorem assumes
all denominators nonzero and allows repeated parameters. Horn–Johnson §0.9.12.
atlas: structured-matrices-def (partial) -/
def cauchyMatrix {m n : Type*} (x : m → ℝ) (y : n → ℝ) : Matrix m n ℝ :=
  fun i j => 1 / (x i + y j)

/-- The Hilbert matrix in zero-based coordinates has entries
`1/(i+j+1)`, equivalent to the usual one-based `1/(i+j-1)`.
Horn–Johnson 2013, §0.9.12.
atlas: structured-matrices-def (partial) -/
def hilbertMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => 1 / ((i.val : ℝ) + (j.val : ℝ) + 1)

/-- Hilbert is a Cauchy matrix with shifted row and unshifted column labels.
Horn–Johnson 2013, §0.9.12.
atlas: structured-matrices-def -/
theorem hilbertMatrix_eq_cauchyMatrix (n : ℕ) :
    hilbertMatrix n = cauchyMatrix (fun i : Fin n => (i.val : ℝ) + 1)
      (fun j : Fin n => (j.val : ℝ)) := by
  ext i j
  dsimp [hilbertMatrix, cauchyMatrix]
  congr 1
  ring

private theorem pivotSchur_cauchyMatrix {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (hDen : ∀ i j, x i + y j ≠ 0) :
    pivotSchur (cauchyMatrix x y) =
      Matrix.diagonal (fun i : Fin n => (x i.succ - x 0) / (x i.succ + y 0)) *
        cauchyMatrix (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ) *
          Matrix.diagonal (fun j : Fin n => (y j.succ - y 0) / (x 0 + y j.succ)) := by
  ext i j
  simp only [pivotSchur_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    cauchyMatrix, one_div, inv_inv]
  field_simp [hDen i.succ j.succ, hDen i.succ 0, hDen 0 j.succ]
  ring

/-- One Schur elimination step gives the Cauchy determinant recurrence. The
only divisions are by the assumed nonzero denominators, so repeated x or y
values require no separate branch. Horn–Johnson 2013, §0.9.12. -/
theorem det_cauchyMatrix_succ {n : ℕ} (x y : Fin (n + 1) → ℝ)
    (hDen : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det = 1 / (x 0 + y 0) *
      (∏ i : Fin n, (x i.succ - x 0) / (x i.succ + y 0)) *
      (∏ j : Fin n, (y j.succ - y 0) / (x 0 + y j.succ)) *
      (cauchyMatrix (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ)).det := by
  have hPivot : cauchyMatrix x y 0 0 ≠ 0 := one_div_ne_zero (hDen 0 0)
  rw [det_eq_mul_det_pivotSchur _ hPivot, pivotSchur_cauchyMatrix x y hDen,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  dsimp [cauchyMatrix]
  ring

private theorem det_vandermonde_succ (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (Matrix.vandermonde x).det = (∏ i : Fin n, (x i.succ - x 0)) *
      (Matrix.vandermonde (fun i : Fin n => x i.succ)).det := by
  rw [Matrix.det_vandermonde, Matrix.det_vandermonde, Fin.prod_univ_succ]
  simp only [Fin.Ioi_zero_eq_map, Finset.prod_map, Fin.coe_succEmb, Fin.prod_Ioi_succ]

private theorem prod_denominators_succ (n : ℕ) (x y : Fin (n + 1) → ℝ) :
    (∏ i : Fin (n + 1), ∏ j : Fin (n + 1), (x i + y j)) =
      (x 0 + y 0) * (∏ i : Fin n, (x i.succ + y 0)) *
        (∏ j : Fin n, (x 0 + y j.succ)) *
          (∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ)) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.prod_univ_succ, Finset.prod_mul_distrib]
  ring

/-- Cauchy's determinant is the product of the two Vandermonde determinants
divided by all denominators. Repeated parameters and the empty determinant
are included. Horn–Johnson 2013, §0.9.12.
atlas: structured-matrices-def (partial) -/
theorem det_cauchyMatrix_eq_vandermonde {n : ℕ} (x y : Fin n → ℝ)
    (hDen : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det = (Matrix.vandermonde x).det * (Matrix.vandermonde y).det /
      (∏ i : Fin n, ∏ j : Fin n, (x i + y j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hTail := ih (fun i : Fin n => x i.succ) (fun j : Fin n => y j.succ)
      (fun i j => hDen i.succ j.succ)
    rw [det_cauchyMatrix_succ x y hDen, hTail,
      det_vandermonde_succ n x, det_vandermonde_succ n y,
      prod_denominators_succ n x y, Finset.prod_div_distrib, Finset.prod_div_distrib]
    have hRow : (∏ i : Fin n, (x i.succ + y 0)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hDen i.succ 0)
    have hCol : (∏ j : Fin n, (x 0 + y j.succ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hDen 0 j.succ)
    have hDiag : (∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr
        (fun j _ => hDen i.succ j.succ))
    field_simp [hRow, hCol, hDiag, hDen 0 0]

/-- The usual product-of-differences Cauchy determinant formula. The only
hypotheses are nonzero denominators; neither list needs distinct entries.
Horn–Johnson 2013, §0.9.12.
atlas: structured-matrices-def -/
theorem det_cauchyMatrix_eq_prod_differences {n : ℕ} (x y : Fin n → ℝ)
    (hDen : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det =
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i)) *
        (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i)) /
          (∏ i : Fin n, ∏ j : Fin n, (x i + y j)) := by
  rw [det_cauchyMatrix_eq_vandermonde x y hDen, Matrix.det_vandermonde, Matrix.det_vandermonde]

/-- Ordered Cauchy parameters with positive denominators have positive
determinant, including the empty matrix. Horn–Johnson 2013, §0.9.12. -/
theorem det_cauchyMatrix_pos_of_strictMono {n : ℕ} (x y : Fin n → ℝ)
    (hx : StrictMono x) (hy : StrictMono y) (hDen : ∀ i j, 0 < x i + y j) :
    0 < (cauchyMatrix x y).det := by
  rw [det_cauchyMatrix_eq_prod_differences x y (fun i j => (hDen i j).ne')]
  apply div_pos
  · apply mul_pos <;> apply Finset.prod_pos
    · intro i _
      exact Finset.prod_pos (fun j hj => sub_pos.mpr (hx (Finset.mem_Ioi.mp hj)))
    · intro i _
      exact Finset.prod_pos (fun j hj => sub_pos.mpr (hy (Finset.mem_Ioi.mp hj)))
  · exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => hDen i j))

/-- Every Hilbert determinant is strictly positive, including the empty
determinant one. Horn–Johnson 2013, §0.9.12.
atlas: structured-matrices-def -/
theorem det_hilbertMatrix_pos (n : ℕ) : 0 < (hilbertMatrix n).det := by
  rw [hilbertMatrix_eq_cauchyMatrix]
  apply det_cauchyMatrix_pos_of_strictMono
  · intro i j hij
    have h : (i.val : ℝ) < j.val := by exact_mod_cast hij
    linarith
  · intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  · intro i j
    positivity

end NLAlib
