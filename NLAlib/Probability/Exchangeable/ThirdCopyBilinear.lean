import NLAlib.Probability.Exchangeable.ThirdCopyPairLaw

/-!
# Discrete integration by parts on the genuine resampling triple

The measure-preserving pair-law bridge transfers the canonical regression and
exchangeable bilinear identity to the actual same-index three-copy space.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The original and both replacement sums in the actual resampling triple
are square-integrable whenever the individual summands are. -/
theorem memLp_resamplingTriple_sums
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i)) :
    MemLp resamplingTripleOriginal 2 (resamplingTripleMeasure ν) ∧
      MemLp resamplingTripleFirst 2 (resamplingTripleMeasure ν) ∧
      MemLp resamplingTripleSecond 2 (resamplingTripleMeasure ν) := by
  have hp := identDistrib_resamplingTriple_original_first ν
  have hX := (hp.comp measurable_fst).symm.memLp_snd
    (memLp_independentResamplingOriginal ν hν)
  have hpair := (identDistrib_independentResampling_pair ν).comp measurable_fst
  have hXp := (hp.comp measurable_snd).symm.memLp_snd
    (hpair.memLp_snd (memLp_independentResamplingOriginal ν hν))
  have hXpp := (identDistrib_resamplingTripleSecond_original ν).symm.memLp_snd hX
  exact ⟨hX, hXp, hXpp⟩

/-- The actual triple original has the canonical independent sum's mean. -/
theorem integral_resamplingTripleOriginal_eq_canonical
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    (∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν) =
      ∫ q, independentResamplingOriginal q ∂independentResamplingMeasure ν :=
  ((identDistrib_resamplingTriple_original_first ν).comp measurable_fst).integral_eq

/-- Actual same-index resampling satisfies bilinear discrete integration by
parts for every bounded continuous test, with the exact coefficient `N/2`.
All required moments are derived from the individual summands' second moments.
The test codomain may be any real normed space.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integral_bilin_resamplingTriple
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (g : E → F) (hgc : Continuous g) (C : ℝ) (hgb : ∀ x, ‖g x‖ ≤ C)
    (B : E →L[ℝ] F →L[ℝ] ℂ) :
    (∫ p, B (resamplingTripleOriginal p -
        ∫ q, resamplingTripleOriginal q ∂resamplingTripleMeasure ν)
      (g (resamplingTripleOriginal p)) ∂resamplingTripleMeasure ν) =
      ((Fintype.card ι : ℝ) / 2) •
        ∫ p, B (resamplingTripleOriginal p - resamplingTripleFirst p)
          (g (resamplingTripleOriginal p) - g (resamplingTripleFirst p))
          ∂resamplingTripleMeasure ν := by
  borelize F
  let P := independentResamplingMeasure ν
  let X : ((ι → E) × (ι × (ι → E))) → E := independentResamplingOriginal
  let X' : ((ι → E) × (ι × (ι → E))) → E := independentResamplingPartner
  have hXm : Measurable X := by unfold X independentResamplingOriginal; fun_prop
  have hX : MemLp X 2 P := memLp_independentResamplingOriginal ν hν
  have htest : MemLp (g ∘ X) 2 P := MemLp.of_bound
    (hgc.comp_aestronglyMeasurable hX.aestronglyMeasurable) C
    (Filter.Eventually.of_forall (fun p => hgb _))
  have hcomap : @Measurable ((ι → E) × (ι × (ι → E))) E
      (MeasurableSpace.comap X inferInstance) _ X :=
    measurable_iff_comap_le.mpr le_rfl
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] (g ∘ X) P :=
    (hgc.stronglyMeasurable.comp_measurable hcomap).aestronglyMeasurable
  have h := integral_bilin_exchangeable (identDistrib_independentResampling_pair ν)
    hX g hgc.measurable htest hXm.comap_le hgm (Fintype.card ι : ℝ)⁻¹
    (by positivity) (condExp_independentResampling_sum ν
      (fun i => (hν i).integrable one_le_two)) B
  have hfactor : (2 * (Fintype.card ι : ℝ)⁻¹)⁻¹ = (Fintype.card ι : ℝ) / 2 := by
    rw [mul_inv_rev, inv_inv]
    ring
  rw [hfactor] at h
  have hp := identDistrib_resamplingTriple_original_first ν
  have hleft := (hp.comp (show Measurable (fun p : E × E =>
      B (p.1 - ∫ q, X q ∂P) (g p.1)) by fun_prop)).integral_eq
  have hright := (hp.comp (show Measurable (fun p : E × E =>
      B (p.1 - p.2) (g p.1 - g p.2)) by fun_prop)).integral_eq
  simp only [Function.comp_apply] at hleft hright
  rw [integral_resamplingTripleOriginal_eq_canonical ν]
  change (∫ p, B (resamplingTripleOriginal p - ∫ q, X q ∂P)
    (g (resamplingTripleOriginal p)) ∂resamplingTripleMeasure ν) = _
  rw [hleft, hright]
  exact h

/-- The genuine resampling difference realizes the entire bilinear covariance
tensor, with factor `N/2`, for any two real continuous linear coordinates.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem integral_coordinate_covariance_resamplingTriple
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i)) (u v : E →L[ℝ] ℝ) :
    (∫ p, u (resamplingTripleOriginal p -
        ∫ q, resamplingTripleOriginal q ∂resamplingTripleMeasure ν) *
      v (resamplingTripleOriginal p -
        ∫ q, resamplingTripleOriginal q ∂resamplingTripleMeasure ν)
      ∂resamplingTripleMeasure ν) =
      (Fintype.card ι : ℝ) / 2 *
        ∫ p, u (resamplingTripleOriginal p - resamplingTripleFirst p) *
          v (resamplingTripleOriginal p - resamplingTripleFirst p)
          ∂resamplingTripleMeasure ν := by
  let P := independentResamplingMeasure ν
  let X : ((ι → E) × (ι × (ι → E))) → E := independentResamplingOriginal
  have hXm : Measurable X := by unfold X independentResamplingOriginal; fun_prop
  have hX := memLp_independentResamplingOriginal ν hν
  have hXs : StronglyMeasurable[MeasurableSpace.comap X inferInstance] X :=
    (show @Measurable ((ι → E) × (ι × (ι → E))) E
      (MeasurableSpace.comap X inferInstance) _ X from
      measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  have h := integral_coordinate_covariance_exchangeable
    (identDistrib_independentResampling_pair ν) hX hXm.comap_le hXs
    (Fintype.card ι : ℝ)⁻¹ (by positivity)
    (condExp_independentResampling_sum ν (fun i => (hν i).integrable one_le_two)) u v
  have hfactor : (2 * (Fintype.card ι : ℝ)⁻¹)⁻¹ = (Fintype.card ι : ℝ) / 2 := by
    rw [mul_inv_rev, inv_inv]
    ring
  rw [hfactor] at h
  have hp := identDistrib_resamplingTriple_original_first ν
  have hleft := (hp.comp (show Measurable (fun p : E × E =>
      u (p.1 - ∫ q, X q ∂P) * v (p.1 - ∫ q, X q ∂P)) by fun_prop)).integral_eq
  have hright := (hp.comp (show Measurable (fun p : E × E =>
      u (p.1 - p.2) * v (p.1 - p.2)) by fun_prop)).integral_eq
  simp only [Function.comp_apply] at hleft hright
  rw [integral_resamplingTripleOriginal_eq_canonical ν]
  rw [hleft, hright]
  exact h

/-- Every pair of actual finite real coordinates of the original sum has
covariance exactly `N/2` times the resampling difference's second moment.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem covariance_resamplingTripleOriginal_eval
    {κ : Type*} [Fintype κ]
    (ν : ι → Measure (κ → ℝ)) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : (κ → ℝ) → κ → ℝ) 2 (ν i)) (i j : κ) :
    cov[(fun p : ι × ((ι × Fin 3) → κ → ℝ) => resamplingTripleOriginal p i),
      (fun p : ι × ((ι × Fin 3) → κ → ℝ) => resamplingTripleOriginal p j); resamplingTripleMeasure ν] =
      (Fintype.card ι : ℝ) / 2 *
        ∫ p, (resamplingTripleOriginal p i - resamplingTripleFirst p i) *
          (resamplingTripleOriginal p j - resamplingTripleFirst p j)
          ∂resamplingTripleMeasure ν := by
  have h := integral_coordinate_covariance_resamplingTriple ν hν
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) i)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j)
  have hX := ((memLp_resamplingTriple_sums ν hν).1).integrable one_le_two
  have hi := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) i).integral_comp_comm hX
  have hj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) j).integral_comp_comm hX
  simp only [ContinuousLinearMap.proj_apply] at hi hj
  simpa only [covariance, ContinuousLinearMap.proj_apply, Pi.sub_apply, hi, hj] using h

end NLAlib
