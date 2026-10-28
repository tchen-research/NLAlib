import NLAlib.RandomMatrix.Gaussian.Moments.ComplexSecondMoment
import NLAlib.RandomMatrix.Gaussian.InverseMoments.ComplexMean
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Independent native complex Gaussian regression blocks

The independent bottom Gaussian block contributes a factor two, which cancels
the factor one half in the circular complex inverse-Wishart moment. The
resulting exact regression coefficient is `r/(s-r)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

private theorem normSq_entry_le_frobSq {a b : Type*} [Fintype a] [Fintype b]
    (M : Matrix a b ℂ) (i : a) (j : b) : Complex.normSq (M i j) ≤ frobSq M := by
  rw [Complex.normSq_eq_norm_sq,frobSq_eq_sum_norm_sq]
  exact (Finset.single_le_sum (fun l _ => sq_nonneg ‖M i l‖) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg ‖M k l‖)
      (Finset.mem_univ i))

open scoped Matrix.Norms.L2Operator in
private theorem complex_product_frobSq_pinvR {p : Type*} [Fintype p] {r s d : ℕ}
    (hrs : r+1≤s) (S : Matrix p (Fin d) ℂ) :
    Integrable (fun xy : Matrix (Fin r) (Fin s) ℂ × Matrix (Fin d) (Fin s) ℂ =>
      frobSq (S*xy.2*pinvR xy.1))
      ((circularComplexGaussianMatrix (Fin r) (Fin s)).prod
        (circularComplexGaussianMatrix (Fin d) (Fin s))) ∧
      ∫ xy, frobSq (S*xy.2*pinvR xy.1) ∂((circularComplexGaussianMatrix (Fin r) (Fin s)).prod
        (circularComplexGaussianMatrix (Fin d) (Fin s)))=(r:ℝ)/((s:ℝ)-r)*frobSq S := by
  let μ := circularComplexGaussianMatrix (Fin r) (Fin s)
  let ν := circularComplexGaussianMatrix (Fin d) (Fin s)
  let Φ : Matrix (Fin r) (Fin s) ℂ × Matrix (Fin d) (Fin s) ℂ → ℝ :=
    fun xy => frobSq (S*xy.2*pinvR xy.1)
  have hm : Measurable Φ := measurable_frobSq.comp
    ((measurable_const.matrix_mul measurable_snd).matrix_mul (measurable_pinvR.comp measurable_fst))
  have hinner (X : Matrix (Fin r) (Fin s) ℂ) :=
    integrable_and_integral_frobSq_mul_circularComplexGaussianMatrix_mul S (pinvR X)
  obtain ⟨hXi,hXv⟩ := integrable_and_integral_frobSq_pinvR_circularComplexGaussianMatrix hrs
  have hi : Integrable Φ (μ.prod ν) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun X => (hinner X).1,?_⟩
    refine (hXi.const_mul (2*frobSq S)).congr (Filter.Eventually.of_forall fun X => ?_)
    dsimp only [Φ]
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (frobSq_nonneg _)]
    exact (hinner X).2.symm
  refine ⟨hi,?_⟩
  change (∫ xy, Φ xy ∂μ.prod ν)=_
  rw [integral_prod Φ hi,integral_congr_ae (Filter.Eventually.of_forall fun X => (hinner X).2),
    integral_const_mul,hXv]
  have hrsR : (r:ℝ)+1≤s := by exact_mod_cast hrs
  have hden : (s:ℝ)-r≠0 := ne_of_gt (by linarith)
  field_simp [hden]

open scoped Matrix.Norms.L2Operator in
private theorem complex_product_mul_pinvR_entry {p : Type*} [Fintype p] {r s d : ℕ}
    (hrs : r+1≤s) (S : Matrix p (Fin d) ℂ) (i : p) (j : Fin r) :
    Integrable (fun xy : Matrix (Fin r) (Fin s) ℂ × Matrix (Fin d) (Fin s) ℂ =>
      (S*xy.2*pinvR xy.1) i j)
      ((circularComplexGaussianMatrix (Fin r) (Fin s)).prod
        (circularComplexGaussianMatrix (Fin d) (Fin s))) ∧
      ∫ xy, (S*xy.2*pinvR xy.1) i j ∂((circularComplexGaussianMatrix (Fin r) (Fin s)).prod
        (circularComplexGaussianMatrix (Fin d) (Fin s)))=0 := by
  let μ := (circularComplexGaussianMatrix (Fin r) (Fin s)).prod
    (circularComplexGaussianMatrix (Fin d) (Fin s))
  obtain ⟨hi,hv⟩ := complex_product_frobSq_pinvR hrs S
  have hm : Measurable (fun xy : Matrix (Fin r) (Fin s) ℂ × Matrix (Fin d) (Fin s) ℂ =>
      (S*xy.2*pinvR xy.1) i j) := (Matrix.measurable_entry i j).comp
    ((measurable_const.matrix_mul measurable_snd).matrix_mul (measurable_pinvR.comp measurable_fst))
  have he : Integrable (fun xy : Matrix (Fin r) (Fin s) ℂ × Matrix (Fin d) (Fin s) ℂ =>
      (S*xy.2*pinvR xy.1) i j) μ := ((integrable_const 1).add hi).mono' hm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun xy => by
          have hs := normSq_entry_le_frobSq (S*xy.2*pinvR xy.1) i j
          rw [Complex.normSq_eq_norm_sq] at hs
          change ‖(S*xy.2*pinvR xy.1) i j‖ ≤ 1+frobSq (S*xy.2*pinvR xy.1)
          nlinarith [sq_nonneg (‖(S*xy.2*pinvR xy.1) i j‖-1),norm_nonneg ((S*xy.2*pinvR xy.1) i j)])
  refine ⟨he,?_⟩
  rw [integral_prod _ he]
  have hz (X : Matrix (Fin r) (Fin s) ℂ) :=
    (integrable_and_integral_mul_circularComplexGaussianMatrix_mul_entry S (pinvR X) i j).2
  rw [integral_congr_ae (Filter.Eventually.of_forall hz),integral_zero]

private theorem complex_regression_noise_eq_adjoint {p : Type*} {r s d : ℕ}
    (X : Matrix (Fin r) (Fin s) ℂ) (Y : Matrix (Fin d) (Fin s) ℂ) (D : Matrix (Fin d) p ℂ) :
    pinvL Xᴴ*Yᴴ*D=(Dᴴ*Y*pinvR X)ᴴ := by
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,pinvR_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

open scoped Matrix.Norms.L2Operator in
/-- Independent actual complex Gaussian sketch blocks have exact regression
noise second moment `r/(s-r)` times the residual energy. Rank zero is included. -/
theorem integrable_and_integral_frobSq_complexGaussian_regression_noise
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : Type*} [Fintype p]
    {r s d : ℕ} (hrs : r+1≤s)
    {X : Ω → Matrix (Fin r) (Fin s) ℂ} {Y : Ω → Matrix (Fin d) (Fin s) ℂ}
    (hXY : HasLaw (fun ω => (X ω,Y ω))
      ((circularComplexGaussianMatrix (Fin r) (Fin s)).prod
        (circularComplexGaussianMatrix (Fin d) (Fin s))) μ) (D : Matrix (Fin d) p ℂ) :
    Integrable (fun ω => frobSq (pinvL (X ω)ᴴ*(Y ω)ᴴ*D)) μ ∧
      ∫ ω, frobSq (pinvL (X ω)ᴴ*(Y ω)ᴴ*D) ∂μ=(r:ℝ)/((s:ℝ)-r)*frobSq D := by
  obtain ⟨hi,hv⟩ := complex_product_frobSq_pinvR hrs Dᴴ
  have hm : Measurable (fun xy : Matrix (Fin r) (Fin s) ℂ × Matrix (Fin d) (Fin s) ℂ =>
      frobSq (Dᴴ*xy.2*pinvR xy.1)) := measurable_frobSq.comp
    ((measurable_const.matrix_mul measurable_snd).matrix_mul (measurable_pinvR.comp measurable_fst))
  simp_rw [complex_regression_noise_eq_adjoint,frobSq_conjTranspose]
  constructor
  · rw [← hXY.map_eq] at hi
    exact hi.comp_aemeasurable hXY.aemeasurable
  · exact (hXY.integral_comp hm.aestronglyMeasurable).trans (by simpa only [frobSq_conjTranspose] using hv)

open scoped Matrix.Norms.L2Operator in
/-- The same independent native complex Gaussian regression noise has
integrable entries and exactly zero complex mean. -/
theorem integrable_and_integral_complexGaussian_regression_noise_entry
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : Type*} [Fintype p]
    {r s d : ℕ} (hrs : r+1≤s)
    {X : Ω → Matrix (Fin r) (Fin s) ℂ} {Y : Ω → Matrix (Fin d) (Fin s) ℂ}
    (hXY : HasLaw (fun ω => (X ω,Y ω))
      ((circularComplexGaussianMatrix (Fin r) (Fin s)).prod
        (circularComplexGaussianMatrix (Fin d) (Fin s))) μ) (D : Matrix (Fin d) p ℂ)
    (i : Fin r) (j : p) :
    Integrable (fun ω => (pinvL (X ω)ᴴ*(Y ω)ᴴ*D) i j) μ ∧
      ∫ ω, (pinvL (X ω)ᴴ*(Y ω)ᴴ*D) i j ∂μ=0 := by
  obtain ⟨hi,hv⟩ := complex_product_mul_pinvR_entry hrs Dᴴ j i
  have hm : Measurable (fun xy : Matrix (Fin r) (Fin s) ℂ × Matrix (Fin d) (Fin s) ℂ =>
      (Dᴴ*xy.2*pinvR xy.1) j i) := (Matrix.measurable_entry j i).comp
    ((measurable_const.matrix_mul measurable_snd).matrix_mul (measurable_pinvR.comp measurable_fst))
  have his : Integrable (fun ω => (Dᴴ*Y ω*pinvR (X ω)) j i) μ := by
    rw [← hXY.map_eq] at hi
    exact hi.comp_aemeasurable hXY.aemeasurable
  have hvs : (∫ ω, (Dᴴ*Y ω*pinvR (X ω)) j i ∂μ)=0 :=
    (hXY.integral_comp hm.aestronglyMeasurable).trans hv
  simp_rw [complex_regression_noise_eq_adjoint,Matrix.conjTranspose_apply,RCLike.star_def]
  refine ⟨?_,?_⟩
  · exact ((@RCLike.conjLIE ℂ _).toContinuousLinearEquiv.integrable_comp_iff).mpr his
  rw [integral_conj,hvs,map_zero]

end NLAlib
