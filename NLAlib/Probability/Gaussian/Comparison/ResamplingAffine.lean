import NLAlib.Probability.Exchangeable.ThirdCopyBilinear

/-!
# Exact resampling cancellation along an affine independent perturbation

The first cancellation uses only the actual independent resampling pair and
boundedness of the test. The separate perturbation law may be any probability
law; Gaussianity is needed only for the second Stein cancellation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- The affine point used in the resampling/Gaussian comparison, before
specializing its two coefficients to square roots of the interpolation time. -/
def resamplingAffinePoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : E) (a b : ℝ) (x z : E) : E := μ + a • (x - μ) + b • z

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Both bilinear terms in the resampling cancellation are integrable under
the actual triple times independent perturbation law. Only summand second
moments and the continuous test's global bound are used. -/
theorem integrable_bilin_resamplingAffine
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) [IsProbabilityMeasure γ] (a b : ℝ)
    (f : E → F) (hfc : Continuous f) (C : ℝ) (hfb : ∀ x, ‖f x‖ ≤ C)
    (B : E →L[ℝ] F →L[ℝ] ℂ) :
    let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
    Integrable (fun q => B (resamplingTripleOriginal q.1 - μ)
      (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2)))
      ((resamplingTripleMeasure ν).prod γ) ∧
    Integrable (fun q => B (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
      (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2) -
        f (resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2)))
      ((resamplingTripleMeasure ν).prod γ) := by
  dsimp only
  let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
  have hm := memLp_resamplingTriple_sums ν hν
  have hX := (hm.1.integrable one_le_two).comp_fst γ
  have hXp := (hm.2.1.integrable one_le_two).comp_fst γ
  have hz : AEStronglyMeasurable
      (fun q : (ι × ((ι × Fin 3) → E)) × E => q.2) ((resamplingTripleMeasure ν).prod γ) :=
    (measurable_snd : Measurable
      (fun q : (ι × ((ι × Fin 3) → E)) × E => q.2)).stronglyMeasurable.aestronglyMeasurable
  have hY : AEStronglyMeasurable
      (fun q => μ + a • (resamplingTripleOriginal q.1 - μ) + b • q.2)
      ((resamplingTripleMeasure ν).prod γ) :=
    (aestronglyMeasurable_const.add
      ((hX.aestronglyMeasurable.sub aestronglyMeasurable_const).const_smul a)).add
        (hz.const_smul b)
  have hYp : AEStronglyMeasurable
      (fun q => μ + a • (resamplingTripleFirst q.1 - μ) + b • q.2)
      ((resamplingTripleMeasure ν).prod γ) :=
    (aestronglyMeasurable_const.add
      ((hXp.aestronglyMeasurable.sub aestronglyMeasurable_const).const_smul a)).add
        (hz.const_smul b)
  have hfY := hfc.comp_aestronglyMeasurable hY
  have hfYp := hfc.comp_aestronglyMeasurable hYp
  constructor
  · exact B.integrable_of_bilin_of_bdd_right C (hX.sub (integrable_const μ)) hfY
      (Filter.Eventually.of_forall (fun q => hfb _))
  · apply B.integrable_of_bilin_of_bdd_right (2 * C) (hX.sub hXp) (hfY.sub hfYp)
    filter_upwards [] with q
    exact (norm_sub_le _ _).trans ((add_le_add (hfb _) (hfb _)).trans_eq (by ring))

/-- The genuine discrete-resampling cancellation under the actual product
probability law. The exact coefficient is `N/2`, and the independent additive
perturbation may have any probability law. The displayed integrals are
integrable as a consequence of the bounded test and summand second moments.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integral_bilin_resamplingAffine
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) [IsProbabilityMeasure γ] (a b : ℝ)
    (f : E → F) (hfc : Continuous f) (C : ℝ) (hfb : ∀ x, ‖f x‖ ≤ C)
    (B : E →L[ℝ] F →L[ℝ] ℂ) :
    let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
    (∫ q, B (resamplingTripleOriginal q.1 - μ)
      (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2))
      ∂(resamplingTripleMeasure ν).prod γ) =
      ((Fintype.card ι : ℝ) / 2) •
        ∫ q, B (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
          (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2) -
            f (resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2))
          ∂(resamplingTripleMeasure ν).prod γ := by
  dsimp only
  let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
  have hi := integrable_bilin_resamplingAffine ν hν γ a b f hfc C hfb B
  rw [integral_prod_symm _ hi.1, integral_prod_symm _ hi.2, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with z
  exact integral_bilin_resamplingTriple ν hν
    (fun x => f (resamplingAffinePoint μ a b x z))
    (hfc.comp (by unfold resamplingAffinePoint; fun_prop)) C (fun x => hfb _) B

end NLAlib
