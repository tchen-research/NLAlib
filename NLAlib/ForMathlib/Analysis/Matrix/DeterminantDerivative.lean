import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Jacobi's formula for real paths of real or complex matrices

The determinant is differentiated by its actual continuous multilinear row
map. Entrywise differentiation transports that computation to the spectral
matrix norm, avoiding a matrix norm change in the public path contract.
In particular complex Hermitian paths retain their complex determinant.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The row-replacement determinant sum is the actual adjugate trace pairing,
over both real and complex scalar fields, including empty matrices. -/
theorem sum_det_updateRow_eq_trace_adjugate_mul (A H : Matrix n n 𝕜) :
    (∑ i : n, (A.updateRow i (H i)).det) = (A.adjugate * H).trace := by
  simp_rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose]
  simp only [mulVec, dotProduct, transpose_apply, trace, diag, mul_apply]
  exact Finset.sum_comm

open scoped Matrix.Norms.Elementwise in
private def detRowsContinuous : ContinuousMultilinearMap 𝕜 (fun _ : n => n → 𝕜) 𝕜 :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

open scoped Matrix.Norms.Elementwise in
private theorem hasDerivAt_det_of_entries {A : ℝ → Matrix n n 𝕜}
    {H : Matrix n n 𝕜} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (H i j) t) :
    HasDerivAt (fun s => (A s).det) ((A t).adjugate * H).trace t := by
  have hAe : HasDerivAt A H t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hA i))
  have h := ((detRowsContinuous.hasFDerivAt (A t)).restrictScalars ℝ).comp_hasDerivAt t hAe
  change HasDerivAt (fun s => (A s).det) (detRowsContinuous.linearDeriv (A t) H) t at h
  rw [ContinuousMultilinearMap.linearDeriv_apply] at h
  change HasDerivAt (fun s => (A s).det)
    (∑ i : n, ((A t).updateRow i (H i)).det) t at h
  rwa [sum_det_updateRow_eq_trace_adjugate_mul] at h

open scoped Matrix.Norms.L2Operator in
private local instance : NormedSpace ℝ (Matrix n n 𝕜) where
  toModule := inferInstance
  norm_smul_le r X := by
    rw [← algebraMap_smul 𝕜 r X]
    simpa only [norm_algebraMap'] using norm_smul_le (algebraMap ℝ 𝕜 r) X

open scoped Matrix.Norms.L2Operator in
/-- Jacobi's determinant derivative for a real parameter and actual real or
complex matrices. The input path uses the spectral matrix norm; singular
and empty matrices are included. -/
theorem _root_.HasDerivAt.matrix_det {A : ℝ → Matrix n n 𝕜}
    {H : Matrix n n 𝕜} {t : ℝ} (hA : HasDerivAt A H t) :
    HasDerivAt (fun s => (A s).det) ((A t).adjugate * H).trace t := by
  apply hasDerivAt_det_of_entries
  intro i j
  let L : Matrix n n 𝕜 →L[ℝ] 𝕜 := (Matrix.entryLinearMap ℝ 𝕜 i j).toContinuousLinearMap
  have h := (L.hasFDerivAt (x := A t)).comp_hasDerivAt (f := A) (f' := H) t
    (by convert! hA)
  convert! h using 1

open scoped Matrix.Norms.L2Operator in
/-- For an invertible matrix, the determinant derivative is its determinant
times the inverse trace pairing. The real parameter and complex matrices
are retained, as needed for Hermitian logarithmic potentials. -/
theorem _root_.HasDerivAt.matrix_det_of_isUnit {A : ℝ → Matrix n n 𝕜}
    {H : Matrix n n 𝕜} {t : ℝ} (hA : HasDerivAt A H t) (hAt : IsUnit (A t)) :
    HasDerivAt (fun s => (A s).det) ((A t).det * ((A t)⁻¹ * H).trace) t := by
  have hInv : (A t)⁻¹ = (A t).det⁻¹ • (A t).adjugate := by
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  have hd : (A t).det ≠ 0 := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det (A t)).mp hAt)
  have he : (A t).det * ((A t)⁻¹ * H).trace = ((A t).adjugate * H).trace := by
    rw [hInv, smul_mul, trace_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  rw [he]
  exact hA.matrix_det

open scoped Matrix.Norms.L2Operator in
/-- The logarithm of the real part of a complex determinant has the inverse
trace derivative when the determinant at the evaluation point is positive
real. Positivity is stated for the actual complex determinant. -/
theorem _root_.HasDerivAt.log_re_matrix_det {A : ℝ → Matrix n n 𝕜}
    {H : Matrix n n 𝕜} {t : ℝ} (hA : HasDerivAt A H t)
    (hdet : 0 < (A t).det) :
    HasDerivAt (fun s => Real.log (RCLike.re (A s).det))
      (RCLike.re (((A t)⁻¹ * H).trace)) t := by
  have hp := (RCLike.pos_iff.mp hdet).1
  have hi : IsUnit (A t) := (isUnit_iff_isUnit_det (A t)).mpr (isUnit_iff_ne_zero.mpr hdet.ne')
  have hd := (hA.matrix_det_of_isUnit hi)
  have hr := (RCLike.reCLM.hasFDerivAt.comp_hasDerivAt t hd).log hp.ne'
  have he : RCLike.re ((A t).det * ((A t)⁻¹ * H).trace) /
      RCLike.re (A t).det = RCLike.re (((A t)⁻¹ * H).trace) := by
    rw [RCLike.mul_re, (RCLike.pos_iff.mp hdet).2, zero_mul, sub_zero]
    exact mul_div_cancel_left₀ _ hp.ne'
  simpa only [RCLike.reCLM_apply, Function.comp_apply, he] using hr

end Matrix
