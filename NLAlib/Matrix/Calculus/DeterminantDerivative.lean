import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Matrix.Normed

/-!
# Jacobi's determinant derivative

The determinant is a continuous multilinear map in the rows. Its derivative
is the sum of single-row replacements, equal to the adjugate trace formula.
This includes singular and empty matrices. Atlas `determinant-derivative`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Elementwise
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

private def detRowsContinuous : ContinuousMultilinearMap ℝ (fun _ : n => n → ℝ) ℝ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

/-- The sum of determinants obtained by replacing one row is the adjugate
trace pairing. Horn–Johnson 2013, §0.8.10; determinant-derivative helper. -/
theorem sum_det_updateRow_eq_trace_adjugate_mul (A H : Matrix n n ℝ) :
    (∑ i : n, (A.updateRow i (H i)).det) = (A.adjugate * H).trace := by
  simp_rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.trace, Matrix.diag,
    Matrix.mul_apply]
  exact Finset.sum_comm

/-- Jacobi's formula for a differentiable matrix path applies at every matrix,
including singular matrices and empty indices. Horn–Johnson 2013, §0.8.10.
atlas: determinant-derivative -/
theorem hasDerivAt_det {A : ℝ → Matrix n n ℝ} {H : Matrix n n ℝ} {t : ℝ}
    (hA : HasDerivAt A H t) :
    HasDerivAt (fun s => (A s).det) ((A t).adjugate * H).trace t := by
  have h := (detRowsContinuous.hasFDerivAt (A t)).comp_hasDerivAt t hA
  change HasDerivAt (fun s => (A s).det) (detRowsContinuous.linearDeriv (A t) H) t at h
  rw [ContinuousMultilinearMap.linearDeriv_apply] at h
  change HasDerivAt (fun s => (A s).det) (∑ i : n, ((A t).updateRow i (H i)).det) t at h
  rwa [sum_det_updateRow_eq_trace_adjugate_mul] at h

/-- The logarithmic determinant derivative is the inverse trace pairing when
the determinant is positive. Horn–Johnson 2013, §0.8.10. The proof only needs
nonzero determinant for the derivative of the real logarithm.
atlas: determinant-derivative -/
theorem hasDerivAt_log_det {A : ℝ → Matrix n n ℝ} {H : Matrix n n ℝ} {t : ℝ}
    (hA : HasDerivAt A H t) (hDet : 0 < (A t).det) :
    HasDerivAt (fun s => Real.log (A s).det) ((A t)⁻¹ * H).trace t := by
  have h := (hasDerivAt_det hA).log hDet.ne'
  have hTrace : ((A t)⁻¹ * H).trace = ((A t).adjugate * H).trace / (A t).det := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul, div_eq_inv_mul]
  rwa [← hTrace] at h

/-- The derivative of `det(t I - A)` is the trace of its adjugate, including
the empty matrix. Horn–Johnson 2013, §0.8.10.
atlas: determinant-derivative -/
theorem hasDerivAt_det_smul_one_sub (A : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt (fun s => (s • (1 : Matrix n n ℝ) - A).det)
      (t • (1 : Matrix n n ℝ) - A).adjugate.trace t := by
  have hA : HasDerivAt (fun s : ℝ => s • (1 : Matrix n n ℝ) - A) 1 t := by
    simpa using ((hasDerivAt_id t).smul_const (1 : Matrix n n ℝ)).sub_const A
  simpa only [Matrix.mul_one] using hasDerivAt_det hA

/-- On `Fin (n+1)`, the characteristic determinant derivative is the sum of
the principal minors obtained by deleting one index. At size one these are
the empty determinants; size zero is covered by the adjugate trace theorem.
Horn–Johnson 2013, §0.8.10.
atlas: determinant-derivative -/
theorem hasDerivAt_det_smul_one_sub_sum_principal_minors {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (t : ℝ) :
    HasDerivAt (fun s => (s • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) - A).det)
      (∑ i : Fin (k + 1),
        ((t • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) - A).submatrix
          i.succAbove i.succAbove).det) t := by
  have h := hasDerivAt_det_smul_one_sub A t
  have hTrace : (t • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) - A).adjugate.trace =
      ∑ i : Fin (k + 1),
        ((t • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) - A).submatrix
          i.succAbove i.succAbove).det := by
    simp only [Matrix.trace, Matrix.diag, Matrix.adjugate_fin_succ_eq_det_submatrix]
    apply Finset.sum_congr rfl
    intro i _
    rw [← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rwa [hTrace] at h

end NLAlib
