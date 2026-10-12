import NLAlib.Matrix.Inequalities.HadamardOrder
import NLAlib.Matrix.Basic.SchurComplement
/-!
# Oppenheim's Hadamard determinant inequality

A scalar pivot expresses the product Schur complement as the Hadamard
product of the first Schur complement with the second trailing block plus
a PSD correction. Singular determinant and zero-diagonal cases are direct.
Source: Horn--Johnson (2013), Theorem 7.5.9;
atlas `schur-product-inequalities`.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

private theorem det_mul_prod_diag_le_det_hadamard_fin (N : ℕ) :
    ∀ A B : Matrix (Fin N) (Fin N) ℝ, A.PosDef → B.PosSemidef →
      (∀ i, 0 < B i i) → A.det * (∏ i, B i i) ≤ (A ⊙ B).det := by
  induction N with
  | zero => intro A B _ _ _; simp
  | succ N ih =>
    intro A B hA hB hdiag
    have ha : 0 < A 0 0 := hA.diag_pos
    have hb : 0 < B 0 0 := hdiag 0
    have hS := ((posDef_iff_pivotSchur (isSymm_of_isHermitian hA.isHermitian)).mp hA).2
    let B₂ := B.submatrix Fin.succ Fin.succ
    have hB₂ : B₂.PosSemidef := hB.submatrix Fin.succ
    let u : Fin N → ℝ := fun i => A i.succ 0
    let R : Matrix (Fin N) (Fin N) ℝ := (A 0 0)⁻¹ • vecMulVec u u
    have hR : R.PosSemidef := by
      simpa only [star_trivial] using
        (Matrix.posSemidef_vecMulVec_self_star u).smul (inv_nonneg.mpr ha.le)
    have hsym (j : Fin N) : A 0 j.succ = A j.succ 0 := by
      simpa using hA.isHermitian.apply j.succ 0
    have hPivot : pivotSchur (A ⊙ B) = pivotSchur A ⊙ B₂ + R ⊙ pivotSchur B := by
      ext i j
      simp only [pivotSchur_apply, Matrix.hadamard_apply, Matrix.add_apply,
        B₂, Matrix.submatrix_apply, R, Matrix.smul_apply, Matrix.vecMulVec_apply,
        smul_eq_mul, u, hsym, _root_.mul_inv_rev]
      ring
    have hle : pivotSchur A ⊙ B₂ ≤ pivotSchur (A ⊙ B) := by
      rw [hPivot, Matrix.le_iff, add_sub_cancel_left]
      exact hR.hadamard (posSemidef_pivotSchur hB)
    have hd := det_le_det_of_posSemidef_le (hS.posSemidef.hadamard hB₂) hle
    have hInd := ih (pivotSchur A) B₂ hS hB₂ (fun i => hdiag i.succ)
    rw [det_eq_mul_det_pivotSchur A ha.ne', Fin.prod_univ_succ,
      det_eq_mul_det_pivotSchur (A ⊙ B) (by simpa only [Matrix.hadamard_apply] using (mul_pos ha hb).ne')]
    simp only [Matrix.hadamard_apply]
    calc
      A 0 0 * (pivotSchur A).det * (B 0 0 * ∏ i : Fin N, B i.succ i.succ) =
          (A 0 0 * B 0 0) * ((pivotSchur A).det * ∏ i, B₂ i i) := by dsimp [B₂]; ring
      _ ≤ (A 0 0 * B 0 0) * (pivotSchur A ⊙ B₂).det :=
        mul_le_mul_of_nonneg_left hInd (mul_pos ha hb).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (mul_pos ha hb).le

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Oppenheim's determinant lower bound for two PSD real matrices, including
singular and empty matrices and zero diagonal entries.
Horn--Johnson (2013), Theorem 7.5.9.
atlas: schur-product-inequalities (partial) -/
theorem det_mul_prod_diag_le_det_hadamard {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * (∏ i, B i i) ≤ (A ⊙ B).det := by
  by_cases hdet : A.det = 0
  · rw [hdet, zero_mul]
    exact (hA.hadamard hB).det_nonneg
  by_cases hzero : ∃ i, B i i = 0
  · obtain ⟨i, hi⟩ := hzero
    have hp : (∏ j, B j j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hp, mul_zero]
    exact (hA.hadamard hB).det_nonneg
  have hAPD := hA.posDef_iff_det_ne_zero.mpr hdet
  have hdiag (i : n) : 0 < B i i := lt_of_le_of_ne hB.diag_nonneg
    (Ne.symm (fun hi => hzero ⟨i, hi⟩))
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := det_mul_prod_diag_le_det_hadamard_fin (Fintype.card n) (A.submatrix e e)
    (B.submatrix e e) (hAPD.submatrix e.injective) (hB.submatrix e) (fun i => hdiag (e i))
  rw [Matrix.det_submatrix_equiv_self, ← Matrix.submatrix_hadamard, Matrix.det_submatrix_equiv_self] at h
  simp only [Matrix.submatrix_apply] at h
  rw [e.prod_comp (fun i => B i i)] at h
  exact h

/-- Both Oppenheim lower bounds hold simultaneously, hence their maximum
is bounded by the determinant of the Hadamard product.
Horn--Johnson (2013), Theorem 7.5.9.
atlas: schur-product-inequalities (partial) -/
theorem max_det_mul_prod_diag_le_det_hadamard {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    max (A.det * ∏ i, B i i) (B.det * ∏ i, A i i) ≤ (A ⊙ B).det := by
  apply max_le
  · exact det_mul_prod_diag_le_det_hadamard hA hB
  · simpa only [Matrix.hadamard_comm] using det_mul_prod_diag_le_det_hadamard hB hA

end NLAlib
