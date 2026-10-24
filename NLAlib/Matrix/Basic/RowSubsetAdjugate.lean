import NLAlib.Matrix.Basic.RowSubsetGram

/-!
# Cofactor sums over fixed-size row subsets

Cauchy–Binet for two different data matrices gives a cross-Gram subset normalizer.
Applying that identity to every cofactor proves the full adjugate sum, retaining
all singular subsets, including those of corank one.

Source: Dereziński–Warmuth 2018, Theorem 6 and equations (2)–(3).
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

/-- The cross-Gram matrix of two padded row restrictions. Unlike a single
matrix's Gram, no Hermitian or positivity property is asserted. -/
def rowSubsetCrossGram (A B : Matrix n d 𝕜) (S : Finset n) : Matrix d d 𝕜 :=
  Aᴴ * coordinateSelector S * B

/-- Cross-Gram Cauchy–Binet keeps the determinant product of corresponding
minors and makes their common support explicit. -/
theorem det_rowSubsetCrossGram_eq_sum_minors (A B : Matrix n d 𝕜) (S : Finset n) :
    (rowSubsetCrossGram A B S).det = ∑ J : SizedSubset n d,
      if J.val ⊆ S then star ((A.submatrix (sizedSubsetIndex J) id).det) *
        (B.submatrix (sizedSubsetIndex J) id).det else 0 := by
  have hpad : ((coordinateSelector S : Matrix n n 𝕜) * A)ᴴ * (coordinateSelector S * B) =
      rowSubsetCrossGram A B S := by
    simp only [rowSubsetCrossGram, Matrix.conjTranspose_mul,
      (coordinateSelector_isHermitian (𝕜 := 𝕜) S).eq, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc Aᴴ (coordinateSelector S) (coordinateSelector S), coordinateSelector_mul_self]
  rw [← hpad, det_mul_eq_sum_det_submatrix_mul_det_submatrix]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose,
    det_coordinateSelector_mul_submatrix, det_coordinateSelector_mul_submatrix]
  split_ifs <;> simp

/-- The all-data cross-Gram normalizer on an arbitrary ambient row set.
It is valid for deficient matrices and singular cross-Grams as well. -/
theorem sum_det_rowSubsetCrossGram_powersetCard (A B : Matrix n d 𝕜)
    (T : Finset n) (s : ℕ) (hds : Fintype.card d ≤ s) :
    (∑ S ∈ T.powersetCard s, (rowSubsetCrossGram A B S).det) =
      ((T.card - Fintype.card d).choose (s - Fintype.card d) : 𝕜) *
        (rowSubsetCrossGram A B T).det := by
  classical
  simp_rw [det_rowSubsetCrossGram_eq_sum_minors]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hJT : J.val ⊆ T
  · rw [if_pos hJT, ← Finset.sum_filter, Finset.sum_const,
      Finset.card_filter_powersetCard_subset J.val T s hJT (by simpa only [J.property] using hds)]
    simp only [J.property, nsmul_eq_mul]
  · rw [if_neg hJT, mul_zero]
    apply Finset.sum_eq_zero
    intro S hS
    rw [if_neg (fun hJS => hJT (hJS.trans (Finset.mem_powersetCard.mp hS).1))]

/-- Deleting a Gram row and a Gram column gives the cross-Gram of the two
corresponding column-deleted data matrices. -/
theorem rowSubsetGram_submatrix_succAbove {D : ℕ}
    (X : Matrix n (Fin (D + 1)) 𝕜) (S : Finset n) (i j : Fin (D + 1)) :
    (rowSubsetGram X S).submatrix j.succAbove i.succAbove =
      rowSubsetCrossGram (X.submatrix id j.succAbove) (X.submatrix id i.succAbove) S := by
  ext a b
  simp only [rowSubsetGram, rowSubsetCrossGram, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.conjTranspose_apply, id_eq]

/-- Summing every cofactor counts each `(D-1)`-row minor with its exact
superset multiplicity. This includes singular row subsets and the scalar case. -/
theorem sum_adjugate_rowSubsetGram_powersetCard_fin_succ {D : ℕ}
    (X : Matrix n (Fin (D + 1)) 𝕜) (T : Finset n) (s : ℕ) (hDs : D ≤ s) :
    (∑ S ∈ T.powersetCard s, (rowSubsetGram X S).adjugate) =
      ((T.card - D).choose (s - D) : 𝕜) • (rowSubsetGram X T).adjugate := by
  classical
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Matrix.adjugate_fin_succ_eq_det_submatrix, rowSubsetGram_submatrix_succAbove]
  rw [← Finset.mul_sum]
  rw [sum_det_rowSubsetCrossGram_powersetCard _ _ T s (by simpa using hDs)]
  simp only [Fintype.card_fin]
  ring

/-- The adjugate sum over fixed-size row subsets, on arbitrary finite column
labels. No full-rank or general-position condition is used. The column dimension
is positive; singular adjugates are deliberately retained. -/
theorem sum_adjugate_rowSubsetGram_powersetCard (X : Matrix n d 𝕜)
    (T : Finset n) (s : ℕ) (hd : 0 < Fintype.card d) (hds : Fintype.card d - 1 ≤ s) :
    (∑ S ∈ T.powersetCard s, (rowSubsetGram X S).adjugate) =
      ((T.card - (Fintype.card d - 1)).choose (s - (Fintype.card d - 1)) : 𝕜) •
        (rowSubsetGram X T).adjugate := by
  classical
  obtain ⟨D, hD⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let e : d ≃ Fin (D + 1) := Fintype.equivOfCardEq (by simpa using hD)
  let Y := X.submatrix id e.symm
  have hG (S : Finset n) : rowSubsetGram Y S = (rowSubsetGram X S).submatrix e.symm e.symm := by
    ext i j
    simp only [rowSubsetGram, Y, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.submatrix_apply, id_eq]
  have hsum := sum_adjugate_rowSubsetGram_powersetCard_fin_succ Y T s
    (by simpa only [hD, Nat.succ_sub_one] using hds)
  ext i j
  have h := congrArg (fun M : Matrix (Fin (D + 1)) (Fin (D + 1)) 𝕜 => M (e i) (e j)) hsum
  simpa only [hG, Matrix.adjugate_submatrix_equiv_self, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, hD, Nat.succ_sub_one] using h

end NLAlib
