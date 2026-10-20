import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeSpectralObservables
import NLAlib.Probability.Free.WordNativeModelTransport

/-! # Full two-sided Gaussian/free spectrum comparison

The Gaussian coefficients have their actual joint standard law, and the free
model is evaluated in an arbitrary faithful positive semicircular C-star
probability space. Actual freeness and individual laws derive the model
transport. All tails, true expectation errors and zero variance are included.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder
namespace NLAlib
variable {ι d Ω E : Type*} [Fintype ι] [Fintype d] [DecidableEq d] [Nonempty d]
  [MeasurableSpace Ω] [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

open scoped Matrix.Norms.L2Operator in
/-- The full two-sided Gaussian/free spectral comparison, together with
the minimum-eigenvalue, maximum-eigenvalue and operator-norm tail and mean
corollaries, for actual coefficient parameters and any Gaussian realization.
The explicit universal constant is `10^20`; normalization uses the actual
unnormalized entry covariance and literal bilinear coefficient variance.

Source: Bandeira--Cipolloni--Schroeder--van Handel, arXiv:2406.11453v2,
Theorem 2.2 and Corollary 2.3.
atlas: gaussian-free-spectrum-two-sided -/
theorem gaussian_free_spectrum_comparison
    (hd : 2 ≤ Fintype.card d) (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (φ : E →ₚ[ℂ] ℂ) (hφ : φ 1=1)
    (hfaithful : ∀ a : E, φ (star a*a)=0 → a=0)
    (S : ι → E) (hS : ∀ i, IsSelfAdjoint (S i))
    (hfree : NoncommutativeProbability.IsFreeFamily φ.toLinearMap S)
    (hlaw : ∀ (i : ι) (n : ℕ), φ (S i^n)=if Even n then (catalan (n/2) : ℂ) else 0)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → (ι → ℝ))
    (hg : HasLaw g (gaussianVector ι) μ) :
    let X := fun ω : Ω => A₀+∑ i,g ω i•A i
    let F := CStarMatrix.affineCombination ℂ A₀ A S
    let ξ := Real.sqrt (Real.sqrt (specNorm (coefficientVariance A))*Real.sqrt (specNorm (coefficientCovariance A)))
    let r := (100000000000000000000 : ℝ)*ξ*Real.log (Fintype.card d : ℝ)^(3/4 : ℝ)
    let b := (100000000000000000000 : ℝ)*Real.sqrt (bilinearSquareMass A Finset.univ)
    (∫ ω : Ω,Metric.hausdorffDist (spectrum ℝ (X ω)) (spectrum ℝ F) ∂μ) ≤ r ∧
    |(∫ ω : Ω,lambdaMin (X ω) ∂μ)-sInf (spectrum ℝ F)| ≤ r ∧
    |(∫ ω : Ω,lambdaMax (X ω) ∂μ)-sSup (spectrum ℝ F)| ≤ r ∧
    |(∫ ω : Ω,specNorm (X ω) ∂μ)-‖F‖| ≤ r ∧
    ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | r+b*t < Metric.hausdorffDist (spectrum ℝ (X ω)) (spectrum ℝ F)} ≤ Real.exp (-t^2) ∧
      μ.real {ω | r+b*t < |lambdaMin (X ω)-sInf (spectrum ℝ F)|} ≤ Real.exp (-t^2) ∧
      μ.real {ω | r+b*t < |lambdaMax (X ω)-sSup (spectrum ℝ F)|} ≤ Real.exp (-t^2) ∧
      μ.real {ω | r+b*t < |specNorm (X ω)-‖F‖|} ≤ Real.exp (-t^2) := by
  classical
  dsimp only
  have hs := spectrum_affineCombination_eq_wordNativeMatrixLinearCombination
    φ hφ hfaithful S hS hfree hlaw A₀ hA₀ A hA
  have hn := norm_affineCombination_eq_wordNativeMatrixLinearCombination
    φ hφ hfaithful S hS hfree hlaw A₀ hA₀ A hA
  simp only [hs,hn]
  let X := fun x : ι → ℝ => A₀+∑ i,x i•A i
  let F := wordNativeMatrixLinearCombination A₀ A
  let H := fun x : ι → ℝ => Metric.hausdorffDist (spectrum ℝ (X x)) (spectrum ℝ F)
  let ξ := Real.sqrt (Real.sqrt (specNorm (coefficientVariance A))*Real.sqrt (specNorm (coefficientCovariance A)))
  let r := (100000000000000000000 : ℝ)*ξ*Real.log (Fintype.card d : ℝ)^(3/4 : ℝ)
  let b := (100000000000000000000 : ℝ)*Real.sqrt (bilinearSquareMass A Finset.univ)
  have hHerm (x : ι → ℝ) : (X x).IsHermitian :=
    hA₀.add (isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _))
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
  have hHc : Continuous H := by
    have hh := (continuous_hausdorffDist_spectrum_selfAdjointPart (spectrum ℝ F)).comp hXc
    convert hh using 1
    funext x
    change Metric.hausdorffDist (spectrum ℝ (X x)) (spectrum ℝ F) =
      Metric.hausdorffDist (spectrum ℝ (selfAdjointPart ℝ (X x) : Matrix d d ℂ)) (spectrum ℝ F)
    rw [(hHerm x).isSelfAdjoint.coe_selfAdjointPart_apply ℝ]
  have hint (f : (ι → ℝ) → ℝ) (hf : Continuous f) :
      (∫ ω : Ω,f (g ω) ∂μ) = ∫ x : ι → ℝ,f x ∂gaussianVector ι := by
    simpa only [Function.comp_def] using hg.integral_comp hf.measurable.aestronglyMeasurable
  have hprob (f : (ι → ℝ) → ℝ) (hf : Continuous f) (u : ℝ) :
      μ.real {ω | u < f (g ω)} = (gaussianVector ι).real {x | u < f x} :=
    hg.measureReal_eq (measurableSet_lt measurable_const hf.measurable)
  have hHD := gaussian_free_hausdorffDist_le_with_probability_and_mean hd A₀ hA₀ A hA
  dsimp only at hHD
  have hHDmean : (∫ x,H x ∂gaussianVector ι) ≤ r := by
    simpa only [H,X,F,r,ξ,mul_assoc] using hHD.1
  have hHDtail : ∀ t : ℝ, 0 ≤ t →
      (gaussianVector ι).real {x | r+b*t < H x} ≤ Real.exp (-t^2) := by
    simpa only [H,X,F,r,b,ξ,mul_assoc] using hHD.2
  obtain ⟨hMin,hMax,hNorm⟩ := gaussian_free_spectral_observables_mean_and_tail hd A₀ hA₀ A hA
  dsimp only at hMin hMax hNorm
  change (∫ ω : Ω,H (g ω) ∂μ) ≤ r ∧
    |(∫ ω : Ω,lambdaMin (X (g ω)) ∂μ)-sInf (spectrum ℝ F)| ≤ r ∧
    |(∫ ω : Ω,lambdaMax (X (g ω)) ∂μ)-sSup (spectrum ℝ F)| ≤ r ∧
    |(∫ ω : Ω,specNorm (X (g ω)) ∂μ)-‖F‖| ≤ r ∧
    ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | r+b*t < H (g ω)} ≤ Real.exp (-t^2) ∧
      μ.real {ω | r+b*t < |lambdaMin (X (g ω))-sInf (spectrum ℝ F)|} ≤ Real.exp (-t^2) ∧
      μ.real {ω | r+b*t < |lambdaMax (X (g ω))-sSup (spectrum ℝ F)|} ≤ Real.exp (-t^2) ∧
      μ.real {ω | r+b*t < |specNorm (X (g ω))-‖F‖|} ≤ Real.exp (-t^2)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hint H hHc]
    exact hHDmean
  · rw [hint _ hMinC]
    exact hMin.1
  · rw [hint _ hMaxC]
    exact hMax.1
  · rw [hint _ hNormC]
    exact hNorm.1
  · intro t ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hprob H hHc]
      exact hHDtail t ht
    · rw [hprob (fun x => |lambdaMin (X x)-sInf (spectrum ℝ F)|)
        (hMinC.sub continuous_const).abs (r+b*t)]
      exact hMin.2 t ht
    · rw [hprob (fun x => |lambdaMax (X x)-sSup (spectrum ℝ F)|)
        (hMaxC.sub continuous_const).abs (r+b*t)]
      exact hMax.2 t ht
    · rw [hprob (fun x => |specNorm (X x)-‖F‖|)
        (hNormC.sub continuous_const).abs (r+b*t)]
      exact hNorm.2 t ht

end NLAlib
