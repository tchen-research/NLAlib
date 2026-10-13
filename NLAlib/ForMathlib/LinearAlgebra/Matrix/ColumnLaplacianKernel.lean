import NLAlib.ForMathlib.LinearAlgebra.Matrix.ColumnLaplacian
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# Positive kernel of a strict column Laplacian

Signed principal cofactors give an explicit positive, normalized right nullvector.
Source: focused polynomial-approximation rederivations, `polyretry:positive-q-relation`.
-/

noncomputable section

open Finset Matrix

namespace NLAlib

/-- A left nullvector of a strict column Laplacian is constant.
Source: the finite maximum principle. -/
theorem strictColumnLaplacian_vecMul_zero_constant {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hpos : ∀ i j, i ≠ j → 0 < A i j) (hsum : ∀ j, ∑ i, A i j = 0)
    {v : Fin (n + 1) → ℝ} (hv : v ᵥ* A = 0) : ∀ i j, v i = v j := by
  obtain ⟨j, hj, hmax⟩ := exists_max_image univ v univ_nonempty
  have hweighted : (∑ i, (v i - v j) * A i j) = 0 := by
    simp only [sub_mul, sum_sub_distrib, ← mul_sum, hsum, mul_zero, sub_zero]
    exact congrFun hv j
  have hnonpos : ∀ i ∈ univ, (v i - v j) * A i j ≤ 0 := by
    intro i hi
    by_cases hij : i = j
    · simp [hij]
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmax i hi)) (hpos i j hij).le
  have hterms := (sum_eq_zero_iff_of_nonpos hnonpos).mp hweighted
  have heq : ∀ i, v i = v j := by
    intro i
    by_cases hij : i = j
    · rw [hij]
    · have h := hterms i (mem_univ i)
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (hpos i j hij).ne')
  intro i k
  exact (heq i).trans (heq k).symm

/-- A zero-column-sum matrix has zero determinant.
Source: its all-ones left nullvector. -/
theorem det_eq_zero_of_column_sum_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hsum : ∀ j, ∑ i, A i j = 0) : A.det = 0 := by
  have hzero : A.transpose *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    ext j
    simp only [mulVec, dotProduct, transpose_apply, mul_one, hsum, Pi.zero_apply]
  have h := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hzero
    (i := (0 : Fin (n + 1))) (by exact (nonZeroDivisors ℝ).one_mem)
  simpa only [det_transpose] using h

/-- Every row of the adjugate of a strict column Laplacian is constant.
Source: the adjugate identities and finite maximum principle. -/
theorem strictColumnLaplacian_adjugate_row_constant {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hpos : ∀ i j, i ≠ j → 0 < A i j) (hsum : ∀ j, ∑ i, A i j = 0)
    (i j k : Fin (n + 1)) : A.adjugate i j = A.adjugate i k := by
  have hd := det_eq_zero_of_column_sum_zero A hsum
  have hmul := Matrix.adjugate_mul A
  rw [hd, zero_smul] at hmul
  have hv : (fun j => A.adjugate i j) ᵥ* A = 0 := by
    ext j
    exact congrFun (congrFun hmul i) j
  exact strictColumnLaplacian_vecMul_zero_constant A hpos hsum hv j k

/-- The signed diagonal adjugate entries are strictly positive.
Source: the positive deleted-principal-cofactor certificate. -/
theorem strictColumnLaplacian_signed_adjugate_diag_pos {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hpos : ∀ i j, i ≠ j → 0 < A i j) (hsum : ∀ j, ∑ i, A i j = 0)
    (i : Fin (n + 1)) : 0 < (-1 : ℝ) ^ n * A.adjugate i i := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have heven : (-1 : ℝ) ^ ((i : ℕ) + i) = 1 := by
    rw [show (i : ℕ) + i = 2 * i by omega, pow_mul]
    norm_num
  rw [heven, one_mul]
  exact strictColumnLaplacian_signed_det_minor_pos A hpos hsum i

/-- Signed principal cofactors form a strictly positive right nullvector.
Source: focused rederivations, equation `polyretry:laplacian-cofactor`. -/
theorem strictColumnLaplacian_mulVec_signed_adjugate_diag_eq_zero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hpos : ∀ i j, i ≠ j → 0 < A i j) (hsum : ∀ j, ∑ i, A i j = 0) :
    A *ᵥ (fun i => (-1 : ℝ) ^ n * A.adjugate i i) = 0 := by
  have hd := det_eq_zero_of_column_sum_zero A hsum
  have hmul := Matrix.mul_adjugate A
  rw [hd, zero_smul] at hmul
  ext i
  have hz : (∑ j, A i j * A.adjugate j 0) = 0 := congrFun (congrFun hmul i) 0
  change (∑ j, A i j * ((-1 : ℝ) ^ n * A.adjugate j j)) = 0
  calc
    _ = (-1 : ℝ) ^ n * ∑ j, A i j * A.adjugate j 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [strictColumnLaplacian_adjugate_row_constant A hpos hsum j j 0]
      ring
    _ = 0 := by rw [hz, mul_zero]

/-- A strict column Laplacian has a positive normalized right nullvector, explicitly
obtained by normalizing its signed principal cofactors.
Source: focused rederivations, `polyretry:positive-q-relation`. -/
theorem strictColumnLaplacian_exists_pos_kernel_sum_one {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hpos : ∀ i j, i ≠ j → 0 < A i j) (hsum : ∀ j, ∑ i, A i j = 0) :
    ∃ w : Fin (n + 1) → ℝ, (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ A *ᵥ w = 0 := by
  let p := fun i => (-1 : ℝ) ^ n * A.adjugate i i
  have hp : ∀ i, 0 < p i := strictColumnLaplacian_signed_adjugate_diag_pos A hpos hsum
  have hs : 0 < ∑ i, p i := sum_pos (fun i hi => hp i) univ_nonempty
  refine ⟨fun i => p i / ∑ j, p j, fun i => div_pos (hp i) hs, ?_, ?_⟩
  · rw [← sum_div]
    exact div_self hs.ne'
  · have hk := strictColumnLaplacian_mulVec_signed_adjugate_diag_eq_zero A hpos hsum
    ext i
    change (∑ j, A i j * (p j / ∑ k, p k)) = 0
    simp only [← mul_div_assoc, ← sum_div]
    rw [show (∑ j, A i j * p j) = 0 from congrFun hk i, zero_div]

end NLAlib
