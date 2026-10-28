import NLAlib.RandomMatrix.Gaussian.Basic.ComplexFullRank
import NLAlib.RandomMatrix.Gaussian.InverseMoments.ComplexResidual
import NLAlib.Matrix.Measurability.GramPseudoinverse
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Native complex inverse-Wishart trace and pseudoinverse moment

The diagonal Schur residual has `k-r+1` circular complex coordinates. Its
reciprocal mean is therefore `1/(2(k-r))`; summing the diagonal gives
`E ||G†||_F² = r/(2(k-r))`. Complex Gaussian matrix entries here have independent
variance-one real and imaginary parts. The unit-variance scaling is handled
separately and doubles the pseudoinverse squared norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder
namespace NLAlib

private theorem measurable_re_inv_rowGram_diagonal {r k : ℕ} (i : Fin r) :
    Measurable (fun G : Matrix (Fin r) (Fin k) ℂ => ((G*Gᴴ)⁻¹ i i).re) :=
  Complex.measurable_re.comp ((Matrix.measurable_entry i i).comp
    (measurable_matrix_inv.comp (measurable_id.matrix_mul Matrix.measurable_conjTranspose)))

private theorem integrable_and_integral_re_inv_rowGram_diagonal_succ
    {n k : ℕ} (hnk : n+2 ≤ k) (i : Fin (n+1)) :
    Integrable (fun G : Matrix (Fin (n+1)) (Fin k) ℂ => ((G*Gᴴ)⁻¹ i i).re)
      (circularComplexGaussianMatrix (Fin (n+1)) (Fin k)) ∧
      ∫ G, ((G*Gᴴ)⁻¹ i i).re ∂circularComplexGaussianMatrix (Fin (n+1)) (Fin k) =
        1/(2*((k:ℝ)-n-1)) := by
  rw [integrable_circularComplexGaussianMatrix_iff, integral_circularComplexGaussianMatrix_eq]
  let μ := circularComplexGaussianVector (Fin k)
  let ν := Measure.pi fun _ : Fin n => μ
  let F : (Fin (n+1) → Fin k → ℂ) → ℝ := fun G =>
    ((Matrix.of G*(Matrix.of G)ᴴ)⁻¹ i i).re
  have hFm : Measurable F := (measurable_re_inv_rowGram_diagonal i).comp Matrix.measurable_of
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Fin k → ℂ) i
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (n+1) => μ) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i
  let Φ : (Fin k → ℂ) × (Fin n → Fin k → ℂ) → ℝ := fun p => F (e.symm p)
  have hΦm : Measurable Φ := hFm.comp e.symm.measurable
  have hΦnn (p) : 0 ≤ Φ p :=
    (RCLike.nonneg_iff.mp ((Matrix.posSemidef_self_mul_conjTranspose (Matrix.of (e.symm p))).inv.diag_nonneg)).1
  have hschur (H : Fin n → Fin k → ℂ)
      (hH : IsUnit (Matrix.of H*(Matrix.of H)ᴴ)) (g : Fin k → ℂ) :
      Φ (g,H)=((gramRowResidual (Matrix.of H) (star g)).re)⁻¹ := by
    let G0 : Fin (n+1) → Fin k → ℂ := Fin.insertNth i g H
    have hsub : (Matrix.of G0).submatrix i.succAbove id=Matrix.of H := by
      ext a b
      simp [G0]
    have hrow : Matrix.of G0 i=g := by funext b; simp [G0]
    have hh : IsUnit ((Matrix.of G0).submatrix i.succAbove id*
        ((Matrix.of G0).submatrix i.succAbove id)ᴴ) := by rwa [hsub]
    have hd := inv_self_mul_conjTranspose_apply_self (Matrix.of G0) i hh
    rw [hsub,hrow, ← gramRowResidual_ofReal_re (Matrix.of H) hH (star g),
      ← Complex.ofReal_inv] at hd
    have hv := congrArg Complex.re hd
    simp only [Complex.ofReal_re] at hv
    change ((Matrix.of G0*(Matrix.of G0)ᴴ)⁻¹ i i).re = _
    exact hv
  have hfull : ∀ᵐ H ∂ν, IsUnit (Matrix.of H*(Matrix.of H)ᴴ) := by
    have hm := (measurePreserving_ofMeasurableEquiv_circularComplexGaussianMatrix
      (m := Fin n) (n := Fin k)).quasiMeasurePreserving.ae
      (circularComplexGaussianMatrix_ae_isUnit_mul_conjTranspose (by omega : n≤k))
    simpa only [Matrix.coe_ofMeasurableEquiv] using hm
  have hinner : ∀ᵐ H ∂ν, Integrable (fun g => Φ (g,H)) μ ∧
      ∫ g, Φ (g,H) ∂μ=1/(2*((k:ℝ)-n-1)) := by
    filter_upwards [hfull] with H hH
    simp_rw [hschur H hH]
    exact integrable_and_integral_inv_re_gramRowResidual_star_circularComplexGaussianVector hnk (Matrix.of H) hH
  have hint : Integrable Φ (μ.prod ν) := by
    rw [integrable_prod_iff' hΦm.aestronglyMeasurable]
    refine ⟨hinner.mono fun _ h => h.1, ?_⟩
    refine (integrable_const (1/(2*((k:ℝ)-n-1)))).congr ?_
    filter_upwards [hinner] with H hH
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (hΦnn _)]
    exact hH.2.symm
  constructor
  · have h := (hmp.integrable_comp_emb e.measurableEmbedding (g := Φ)).mpr hint
    refine h.congr (Filter.Eventually.of_forall fun G => ?_)
    simp [Φ,F]
  · have h := hmp.integral_comp' Φ
    simp only [Φ,MeasurableEquiv.symm_apply_apply] at h
    rw [h,integral_prod_symm Φ hint,integral_congr_ae (hinner.mono fun _ h => h.2)]
    simp

/-- Every diagonal entry of the inverse native circular-complex Wishart Gram
matrix has integrable real part and exact mean `1/(2(k-r))`. -/
theorem integrable_and_integral_re_inv_rowGram_diagonal_circularComplexGaussianMatrix
    {r k : ℕ} (hrk : r+1 ≤ k) (i : Fin r) :
    Integrable (fun G : Matrix (Fin r) (Fin k) ℂ => ((G*Gᴴ)⁻¹ i i).re)
      (circularComplexGaussianMatrix (Fin r) (Fin k)) ∧
      ∫ G, ((G*Gᴴ)⁻¹ i i).re ∂circularComplexGaussianMatrix (Fin r) (Fin k) =
        1/(2*((k:ℝ)-r)) := by
  cases r with
  | zero => exact i.elim0
  | succ n =>
    obtain ⟨hi,hv⟩ := integrable_and_integral_re_inv_rowGram_diagonal_succ (by omega) i
    refine ⟨hi,hv.trans ?_⟩
    push_cast
    congr 1
    ring

open scoped Matrix.Norms.L2Operator in
/-- Exact Frobenius pseudoinverse second moment under the native circular
complex Gaussian matrix law, including zero row rank. -/
theorem integrable_and_integral_frobSq_pinvR_circularComplexGaussianMatrix
    {r k : ℕ} (hrk : r+1 ≤ k) :
    Integrable (fun G : Matrix (Fin r) (Fin k) ℂ => frobSq (pinvR G))
      (circularComplexGaussianMatrix (Fin r) (Fin k)) ∧
      ∫ G, frobSq (pinvR G) ∂circularComplexGaussianMatrix (Fin r) (Fin k) =
        (r:ℝ)/(2*((k:ℝ)-r)) := by
  have hd (i : Fin r) :=
    integrable_and_integral_re_inv_rowGram_diagonal_circularComplexGaussianMatrix hrk i
  have he : (fun G : Matrix (Fin r) (Fin k) ℂ => frobSq (pinvR G)) =
      fun G => ∑ i, ((G*Gᴴ)⁻¹ i i).re := by
    funext G
    rw [frobSq_pinvR_eq_trace_inv]
    change ((G*Gᴴ)⁻¹).trace.re = _
    simp only [Matrix.trace,Complex.re_sum,Matrix.diag_apply]
  rw [he]
  refine ⟨integrable_finsetSum _ fun i _ => (hd i).1,?_⟩
  rw [integral_finsetSum _ fun i _ => (hd i).1]
  simp only [(hd _).2, Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

open scoped Matrix.Norms.L2Operator in
/-- The native circular-complex Frobenius inverse moment transports to any
sample space with its exact Gaussian matrix law. -/
theorem integrable_and_integral_frobSq_pinvR_circularComplexGaussianMatrix_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {r k : ℕ}
    {G : Ω → Matrix (Fin r) (Fin k) ℂ}
    (hG : HasLaw G (circularComplexGaussianMatrix (Fin r) (Fin k)) μ) (hrk : r+1≤k) :
    Integrable (fun ω => frobSq (pinvR (G ω))) μ ∧
      ∫ ω, frobSq (pinvR (G ω)) ∂μ=(r:ℝ)/(2*((k:ℝ)-r)) := by
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_pinvR_circularComplexGaussianMatrix hrk
  have hm : Measurable (fun G : Matrix (Fin r) (Fin k) ℂ => frobSq (pinvR G)) :=
    measurable_frobSq.comp measurable_pinvR
  constructor
  · rw [← hG.map_eq] at hi
    exact hi.comp_aemeasurable hG.aemeasurable
  · exact (hG.integral_comp hm.aestronglyMeasurable).trans hv

end NLAlib
