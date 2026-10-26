import NLAlib.Krylov.Processes.Bidiagonalization

/-!
# The actual Golub--Kahan decomposition

The native recurrence is a witness for `GolubKahanDecomp`. Consequently its
matrices satisfy the two bidiagonalization relations, including the actual last
right-vector residual in the transpose relation.
Source: Golub--Van Loan (2013), Section 10.4.1, equations (10.4.4)--(10.4.5).
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The actual recurrence supplies a bidiagonalization witness with `k+1` left
vectors and `k` right vectors. The success convention also computes the next right
vector, which supplies the transpose residual.
atlas: golub-kahan-bidiagonalization (partial) -/
def golubKahanRecurrenceDecomp (A : Matrix m n ℝ) (b : m → ℝ) (k : ℕ)
    (h : GolubKahanSucceeds A b k) : GolubKahanDecomp A b k where
  U := golubKahanU A b (k + 1)
  V := golubKahanV A b k
  gradedU := (isGradedKrylovBasis_golubKahanU_V h).1
  gradedV := (isGradedKrylovBasis_golubKahan_of_dilationGrade
    (show 2 * k ≤ krylovGrade (dilation A) (Sum.elim b (0 : n → ℝ)) from
      (by have := two_mul_le_dilationGrade_of_golubKahanSucceeds h; omega))).2

/-- The recurrence's bidiagonal compression has its actual diagonal coefficients.
atlas: golub-kahan-recurrence (partial)
atlas: golub-kahan-bidiagonalization (partial) -/
theorem golubKahanRecurrenceDecomp_B_diag (A : Matrix m n ℝ) (b : m → ℝ) (k : ℕ)
    (h : GolubKahanSucceeds A b k) (j : Fin k) :
    (golubKahanRecurrenceDecomp A b k h).B j.castSucc j =
      (golubKahanRecurrence A b j).alpha := by
  rw [GolubKahanDecomp.B, transpose_mul_mul_apply_eq_dotProduct]
  exact dotProduct_golubKahan_eq_alpha A b j

/-- The recurrence's bidiagonal compression has its actual subdiagonal coefficients.
atlas: golub-kahan-recurrence (partial)
atlas: golub-kahan-bidiagonalization (partial) -/
theorem golubKahanRecurrenceDecomp_B_subdiag (A : Matrix m n ℝ) (b : m → ℝ) (k : ℕ)
    (h : GolubKahanSucceeds A b k) (j : Fin k) :
    (golubKahanRecurrenceDecomp A b k h).B j.succ j =
      (golubKahanRecurrence A b (j + 1)).beta := by
  rw [GolubKahanDecomp.B, transpose_mul_mul_apply_eq_dotProduct]
  exact dotProduct_golubKahan_eq_beta A b j

/-- The transpose relation in column form has exactly the next right-vector
residual in the last column. This includes `k = 0`, where the prefix is empty.
atlas: golub-kahan-bidiagonalization (partial) -/
theorem golubKahanRecurrenceDecomp_transpose_mulVec (A : Matrix m n ℝ) (b : m → ℝ)
    (k : ℕ) (h : GolubKahanSucceeds A b k) (j : Fin (k + 1)) :
    Aᵀ *ᵥ (golubKahanRecurrenceDecomp A b k h).U.col j =
      (golubKahanRecurrenceDecomp A b k h).V *ᵥ
        (golubKahanRecurrenceDecomp A b k h).Bᵀ.col j +
      if j = Fin.last k then
        (golubKahanRecurrence A b k).alpha • (golubKahanRecurrence A b k).v else 0 := by
  let D := golubKahanRecurrenceDecomp A b k h
  have hV := (isGradedKrylovBasis_golubKahanU_V h).2
  have hm : Aᵀ *ᵥ D.U.col j ∈ krylovSpace (Aᵀ * A) (Aᵀ *ᵥ b) (k + 1) :=
    krylovSpace_mono _ _ (by omega)
      (transpose_mulVec_mem_krylovSpace A b (D.gradedU.col_mem j))
  have he := hV.eq_sum_of_mem hm
  rw [Fin.sum_univ_castSucc] at he
  have hfirst : ∀ l : Fin k,
      (golubKahanV A b (k + 1)).col l.castSucc ⬝ᵥ (Aᵀ *ᵥ D.U.col j) = D.B j l := by
    intro l
    rw [Matrix.dotProduct_transpose_mulVec, GolubKahanDecomp.B,
      transpose_mul_mul_apply_eq_dotProduct]
    rfl
  have hlast : (golubKahanV A b (k + 1)).col (Fin.last k) ⬝ᵥ
      (Aᵀ *ᵥ D.U.col j) = if j = Fin.last k then (golubKahanRecurrence A b k).alpha else 0 := by
    by_cases hj : j = Fin.last k
    · subst j
      rw [if_pos rfl, Matrix.dotProduct_transpose_mulVec]
      exact dotProduct_golubKahan_eq_alpha A b k
    · rw [if_neg hj]
      have hjk : (j : ℕ) ≠ k := by
        intro heq
        exact hj (Fin.ext heq)
      exact hV.col_dotProduct_eq_zero (Fin.last k)
        (krylovSpace_mono _ _ (by have := j.isLt; simp only [Fin.val_last]; omega)
          (transpose_mulVec_mem_krylovSpace A b (D.gradedU.col_mem j)))
  simp_rw [hfirst] at he
  rw [hlast] at he
  change Aᵀ *ᵥ D.U.col j = D.V *ᵥ D.Bᵀ.col j + _
  rw [he, mulVec_eq_sum_smul_col]
  congr 1
  split_ifs
  · rfl
  · exact zero_smul _ _

end NLAlib
