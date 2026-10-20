import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeHausdorff
import NLAlib.ForMathlib.Analysis.CStarAlgebra.SpectralHausdorff

/-! # Actual Gaussian/free spectral observables

Native spectral Hausdorff distance dominates the lower edge, upper edge
and operator norm errors. The expected observable differences are true
Bochner means, with integrability derived rather than assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

private theorem observable_mean_tail_of_abs_sub_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f H : Ω → ℝ) (c r b : ℝ) (hf : AEMeasurable f μ) (hH : Integrable H μ)
    (hdom : ∀ x, |f x-c| ≤ H x) (hmean : (∫ x,H x ∂μ) ≤ r)
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {x | r+b*t < H x} ≤ Real.exp (-t^2)) :
    |(∫ x,f x ∂μ)-c| ≤ r ∧
      ∀ t : ℝ, 0 ≤ t → μ.real {x | r+b*t < |f x-c|} ≤ Real.exp (-t^2) := by
  have hD : Integrable (fun x => f x-c) μ := hH.mono'
    (hf.sub_const c).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hdom x)
  have hfi : Integrable f μ := by
    simpa only [Pi.add_def,sub_add_cancel] using hD.add (integrable_const c)
  have he : (∫ x,f x-c ∂μ) = (∫ x,f x ∂μ)-c := by
    rw [integral_sub hfi (integrable_const c),integral_const,probReal_univ,one_smul]
  refine ⟨?_, ?_⟩
  · calc
      _ = |∫ x,f x-c ∂μ| := congrArg abs he.symm
      _ ≤ ∫ x,|f x-c| ∂μ := by simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => f x-c)
      _ ≤ ∫ x,H x ∂μ := integral_mono hD.abs hH hdom
      _ ≤ r := hmean
  · intro t ht
    refine le_trans ?_ (htail t ht)
    apply measureReal_mono _ (by finiteness)
    intro x hx
    exact lt_of_lt_of_le hx (hdom x)

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [Nonempty d]

open scoped Matrix.Norms.L2Operator in
/-- The actual smallest eigenvalue, largest eigenvalue and operator norm
share the Gaussian/free source tail and expectation bounds. Includes all
zero-variance families and arbitrary deterministic Hermitian means.
Source: arXiv:2406.11453v2, Theorem 2.2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem gaussian_free_spectral_observables_mean_and_tail
    (hd : 2 ≤ Fintype.card d) (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    let X := fun x : ι → ℝ => A₀+∑ i,x i•A i
    let F := wordNativeMatrixLinearCombination A₀ A
    let ξ := Real.sqrt (Real.sqrt (specNorm (coefficientVariance A))*Real.sqrt (specNorm (coefficientCovariance A)))
    let r := (100000000000000000000 : ℝ)*ξ*Real.log (Fintype.card d : ℝ)^(3/4 : ℝ)
    let b := (100000000000000000000 : ℝ)*Real.sqrt (bilinearSquareMass A Finset.univ)
    (|(∫ x : ι → ℝ,lambdaMin (X x) ∂gaussianVector ι)-sInf (spectrum ℝ F)| ≤ r ∧
      ∀ t : ℝ, 0 ≤ t → (gaussianVector ι).real {x | r+b*t < |lambdaMin (X x)-sInf (spectrum ℝ F)|} ≤ Real.exp (-t^2)) ∧
    (|(∫ x : ι → ℝ,lambdaMax (X x) ∂gaussianVector ι)-sSup (spectrum ℝ F)| ≤ r ∧
      ∀ t : ℝ, 0 ≤ t → (gaussianVector ι).real {x | r+b*t < |lambdaMax (X x)-sSup (spectrum ℝ F)|} ≤ Real.exp (-t^2)) ∧
    (|(∫ x : ι → ℝ,specNorm (X x) ∂gaussianVector ι)-‖F‖| ≤ r ∧
      ∀ t : ℝ, 0 ≤ t → (gaussianVector ι).real {x | r+b*t < |specNorm (X x)-‖F‖|} ≤ Real.exp (-t^2)) := by
  classical
  let : Nontrivial (WordHilbertSpace ι) := by
    apply nontrivial_of_ne (wordVacuum ι) 0
    intro hz
    have hn := norm_wordVacuum (ι := ι)
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  dsimp only
  let X := fun x : ι → ℝ => A₀+∑ i,x i•A i
  let F := wordNativeMatrixLinearCombination A₀ A
  let H := fun x : ι → ℝ => Metric.hausdorffDist (spectrum ℝ (X x)) (spectrum ℝ F)
  let ξ := Real.sqrt (Real.sqrt (specNorm (coefficientVariance A))*Real.sqrt (specNorm (coefficientCovariance A)))
  let r := (100000000000000000000 : ℝ)*ξ*Real.log (Fintype.card d : ℝ)^(3/4 : ℝ)
  let b := (100000000000000000000 : ℝ)*Real.sqrt (bilinearSquareMass A Finset.univ)
  have hHerm (x : ι → ℝ) : (X x).IsHermitian :=
    hA₀.add (isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _))
  have hF := isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA
  have hXc : Continuous X := by dsimp only [X]; fun_prop
  have hMaxC : Continuous (fun x => lambdaMax (X x)) := by
    have hh := continuous_lambdaMax_selfAdjointPart.comp hXc
    convert hh using 1
    funext x
    change lambdaMax (X x) = lambdaMax (selfAdjointPart ℝ (X x) : Matrix d d ℂ)
    rw [(hHerm x).isSelfAdjoint.coe_selfAdjointPart_apply ℝ]
  have hMinC : Continuous (fun x => lambdaMin (X x)) := by
    have hh := (continuous_lambdaMax_selfAdjointPart.comp hXc.neg).neg
    convert hh using 1
    funext x
    change lambdaMin (X x) = -lambdaMax (selfAdjointPart ℝ (-X x) : Matrix d d ℂ)
    rw [(hHerm x).neg.isSelfAdjoint.coe_selfAdjointPart_apply ℝ,lambdaMax_neg,neg_neg]
  have hNormC : Continuous (fun x => specNorm (X x)) := by
    simpa only [specNorm_eq_norm] using hXc.norm
  have hHint : Integrable H (gaussianVector ι) :=
    integrable_of_lipschitz_gaussianVector _ _ (Real.sqrt_nonneg _)
      (abs_hausdorffDist_spectrum_affineSeries_sub_le_bilinearSquareMass A₀ hA₀ A hA (spectrum ℝ F))
  have hmain := gaussian_free_hausdorffDist_le_with_probability_and_mean hd A₀ hA₀ A hA
  dsimp only at hmain
  have hmean : (∫ x,H x ∂gaussianVector ι) ≤ r := by
    simpa only [H,r,ξ,mul_assoc] using hmain.1
  have htail : ∀ t : ℝ, 0 ≤ t → (gaussianVector ι).real {x | r+b*t < H x} ≤ Real.exp (-t^2) := by
    simpa only [H,r,b,ξ,mul_assoc] using hmain.2
  have hMinDom (x : ι → ℝ) : |lambdaMin (X x)-sInf (spectrum ℝ F)| ≤ H x := by
    exact (hHerm x).isSelfAdjoint.abs_sInf_spectrum_sub_le_hausdorffDist hF
  have hMaxDom (x : ι → ℝ) : |lambdaMax (X x)-sSup (spectrum ℝ F)| ≤ H x := by
    exact (hHerm x).isSelfAdjoint.abs_sSup_spectrum_sub_le_hausdorffDist hF
  have hNormDom (x : ι → ℝ) : |specNorm (X x)-‖F‖| ≤ H x := by
    simpa only [specNorm_eq_norm] using (hHerm x).isSelfAdjoint.abs_norm_sub_norm_le_hausdorffDist_real_spectrum hF
  exact ⟨observable_mean_tail_of_abs_sub_le (gaussianVector ι) _ H _ r b hMinC.measurable.aemeasurable hHint hMinDom hmean htail,
    observable_mean_tail_of_abs_sub_le (gaussianVector ι) _ H _ r b hMaxC.measurable.aemeasurable hHint hMaxDom hmean htail,
    observable_mean_tail_of_abs_sub_le (gaussianVector ι) _ H _ r b hNormC.measurable.aemeasurable hHint hNormDom hmean htail⟩

end NLAlib
