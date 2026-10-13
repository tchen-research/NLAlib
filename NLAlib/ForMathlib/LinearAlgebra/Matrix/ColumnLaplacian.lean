import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Instances.Matrix
import NLAlib.ForMathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Strict column Laplacians and their cofactors

A real matrix with positive off-diagonal entries and zero column sums has nonsingular
deleted principal minors, with the expected determinant sign.
Source: focused polynomial-approximation rederivations, `polyretry:peak-laplacian`.
-/

noncomputable section

open Finset Matrix

namespace NLAlib

/-- Deleting the same row and column from a strict column Laplacian yields strict column
 diagonal dominance. Source: focused rederivations, `polyretry:peak-laplacian`. -/
theorem strictColumnLaplacian_minor_dominant {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hpos : ∀ i j, i ≠ j → 0 < A i j) (hsum : ∀ j, ∑ i, A i j = 0)
    (k : Fin (n + 1)) (j : Fin n) :
    ∑ i ∈ univ.erase j, ‖A (k.succAbove i) (k.succAbove j)‖ <
      ‖A (k.succAbove j) (k.succAbove j)‖ := by
  have hk : 0 < A k (k.succAbove j) := hpos _ _ (Fin.ne_succAbove _ _)
  have hoff : ∀ i ∈ univ.erase j, 0 < A (k.succAbove i) (k.succAbove j) := by
    intro i hi
    exact hpos _ _ (fun h => (mem_erase.mp hi).1 (Fin.succAbove_right_injective h))
  have hcol := hsum (k.succAbove j)
  rw [Fin.sum_univ_succAbove (fun i => A i (k.succAbove j)) k,
    ← sum_erase_add univ (fun i => A (k.succAbove i) (k.succAbove j)) (mem_univ j)] at hcol
  have hnonneg : 0 ≤ ∑ i ∈ univ.erase j, A (k.succAbove i) (k.succAbove j) :=
    sum_nonneg fun i hi => (hoff i hi).le
  have hd : A (k.succAbove j) (k.succAbove j) < 0 := by linarith
  simp_rw [Real.norm_eq_abs]
  rw [abs_of_neg hd]
  have heq : (∑ i ∈ univ.erase j, |A (k.succAbove i) (k.succAbove j)|) =
      ∑ i ∈ univ.erase j, A (k.succAbove i) (k.succAbove j) :=
    sum_congr rfl fun i hi => abs_of_pos (hoff i hi)
  rw [heq]
  linarith

/-- Every deleted principal minor of a strict column Laplacian is nonsingular.
Source: focused rederivations, `polyretry:peak-laplacian`, via Gershgorin. -/
theorem strictColumnLaplacian_det_minor_ne_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hpos : ∀ i j, i ≠ j → 0 < A i j) (hsum : ∀ j, ∑ i, A i j = 0)
    (k : Fin (n + 1)) : (A.submatrix k.succAbove k.succAbove).det ≠ 0 :=
  det_ne_zero_of_sum_col_lt_diag (strictColumnLaplacian_minor_dominant A hpos hsum k)

private def minorDiagonalHomotopy {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : Fin (n + 1)) (s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then A (k.succAbove i) (k.succAbove j)
    else s * A (k.succAbove i) (k.succAbove j)

private theorem minorDiagonalHomotopy_det_ne_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hpos : ∀ i j, i ≠ j → 0 < A i j) (hsum : ∀ j, ∑ i, A i j = 0)
    (k : Fin (n + 1)) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (minorDiagonalHomotopy A k s).det ≠ 0 := by
  apply det_ne_zero_of_sum_col_lt_diag
  intro j
  have hd := strictColumnLaplacian_minor_dominant A hpos hsum k j
  dsimp [minorDiagonalHomotopy]
  simp only [ite_true]
  apply lt_of_le_of_lt ?_ hd
  apply sum_le_sum
  intro i hi
  have hij := (mem_erase.mp hi).1
  rw [if_neg hij, abs_mul, abs_of_nonneg hs.1]
  change s * ‖A (k.succAbove i) (k.succAbove j)‖ ≤ _
  exact mul_le_of_le_one_left (norm_nonneg _) hs.2

/-- The deleted principal cofactors of a strict column Laplacian have positive signed values.
Source: focused rederivations, equation `polyretry:laplacian-cofactor`. -/
theorem strictColumnLaplacian_signed_det_minor_pos {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hpos : ∀ i j, i ≠ j → 0 < A i j) (hsum : ∀ j, ∑ i, A i j = 0)
    (k : Fin (n + 1)) : 0 < (-1 : ℝ) ^ n * (A.submatrix k.succAbove k.succAbove).det := by
  let f : ℝ → ℝ := fun s => (-1 : ℝ) ^ n * (minorDiagonalHomotopy A k s).det
  have hf : Continuous f := by
    apply Continuous.const_mul
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · simp only [minorDiagonalHomotopy, if_pos hij]
      exact continuous_const
    · simp only [minorDiagonalHomotopy, if_neg hij]
      exact continuous_id.mul continuous_const
  have hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, f s ≠ 0 := fun s hs =>
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (minorDiagonalHomotopy_det_ne_zero A hpos hsum k hs)
  have hf0 : 0 < f 0 := by
    have hzero : minorDiagonalHomotopy A k 0 =
        Matrix.diagonal (fun j => A (k.succAbove j) (k.succAbove j)) := by
      ext i j
      simp only [minorDiagonalHomotopy, Matrix.diagonal_apply]
      split_ifs <;> simp_all
    dsimp [f]
    rw [hzero, Matrix.det_diagonal]
    have hprod : (-1 : ℝ) ^ n * (∏ j : Fin n, A (k.succAbove j) (k.succAbove j)) =
        ∏ j : Fin n, -A (k.succAbove j) (k.succAbove j) := by
      simpa only [card_univ, Fintype.card_fin] using (prod_neg (s := univ)
        (fun j : Fin n => A (k.succAbove j) (k.succAbove j))).symm
    rw [hprod]
    apply prod_pos
    intro j hj
    have hcol := hsum (k.succAbove j)
    rw [Fin.sum_univ_succAbove (fun i => A i (k.succAbove j)) k,
      ← sum_erase_add univ (fun i => A (k.succAbove i) (k.succAbove j)) (mem_univ j)] at hcol
    have hnonneg : 0 ≤ ∑ i ∈ univ.erase j, A (k.succAbove i) (k.succAbove j) := by
      apply sum_nonneg
      intro i hi
      exact (hpos _ _ (fun h => (mem_erase.mp hi).1 (Fin.succAbove_right_injective h))).le
    have hk := hpos k (k.succAbove j) (Fin.ne_succAbove _ _)
    linarith
  have hprod := mul_pos_of_continuousOn_ne_zero hf.continuousOn hne
    (x := 0) (y := 1) (by norm_num) (by norm_num)
  have hf1 : 0 < f 1 := (mul_pos_iff.mp hprod).resolve_right (by intro h; linarith [h.1]) |>.2
  have hone : minorDiagonalHomotopy A k 1 = A.submatrix k.succAbove k.succAbove := by
    ext i j
    simp only [minorDiagonalHomotopy, submatrix_apply, one_mul, ite_self]
  simpa only [f, hone] using hf1

end NLAlib
