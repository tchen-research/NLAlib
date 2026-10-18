import NLAlib.Probability.Gaussian.Comparison.ResamplingStein
import NLAlib.ForMathlib.MeasureTheory.AffineDifferentiation

/-!
# The actual square-root resampling interpolation

Bounded C¹ tests with values in a complete real normed space have a continuous
actual expectation, including
both endpoints. Interior differentiation under the integral and the two
proved Stein cancellations give the exact source derivative formula.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι κ F : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype κ] [DecidableEq κ] [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]

/-- The actual expected primitive along the centered-sum/centered-Gaussian
square-root interpolation, on the genuine triple times independent noise law. -/
def resamplingInterpolation (ν : ι → Measure (κ → ℝ)) (γ : Measure (κ → ℝ))
    (Φ : (κ → ℝ) → K) (t : ℝ) : K :=
  let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
  ∫ q, Φ (resamplingAffinePoint μ (Real.sqrt t) (Real.sqrt (1 - t))
    (resamplingTripleOriginal q.1) q.2) ∂(resamplingTripleMeasure ν).prod γ

omit [DecidableEq κ] in
/-- A bounded continuous primitive gives a continuous interpolation on all
real times, in particular at both endpoints of the unit interval.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem continuous_resamplingInterpolation
    (ν : ι → Measure (κ → ℝ)) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : (κ → ℝ) → κ → ℝ) 2 (ν i))
    (γ : Measure (κ → ℝ)) [IsProbabilityMeasure γ]
    (Φ : (κ → ℝ) → K) (hΦc : Continuous Φ) (CΦ : ℝ) (hΦb : ∀ y, ‖Φ y‖ ≤ CΦ) :
    Continuous (resamplingInterpolation ν γ Φ) := by
  let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
  let P := resamplingTripleMeasure ν
  have hX := ((memLp_resamplingTriple_sums ν hν).1.integrable one_le_two).comp_fst γ
  have hXc := hX.sub (integrable_const μ)
  have hZa : AEStronglyMeasurable
      (fun q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ) => q.2) (P.prod γ) :=
    (measurable_snd : Measurable
      (fun q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ) => q.2)).stronglyMeasurable.aestronglyMeasurable
  have h := continuous_integral_affine_path _ _ hXc.aestronglyMeasurable hZa μ
    Real.sqrt (fun t => Real.sqrt (1 - t)) Real.continuous_sqrt
    (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)) Φ hΦc CΦ hΦb
  exact h

omit [DecidableEq ι] [MeasurableSingletonClass ι] [DecidableEq κ] [CompleteSpace K] in
/-- At time zero the actual interpolation is the centered Gaussian law
translated by the original sum's mean.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem resamplingInterpolation_zero
    (ν : ι → Measure (κ → ℝ)) [∀ i, IsProbabilityMeasure (ν i)]
    (γ : Measure (κ → ℝ)) [IsProbabilityMeasure γ]
    (Φ : (κ → ℝ) → K) (hΦc : Continuous Φ) :
    resamplingInterpolation ν γ Φ 0 =
      ∫ z, Φ ((∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν) + z) ∂γ := by
  let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
  let P := resamplingTripleMeasure ν
  have hf0 : Continuous (fun z : κ → ℝ => Φ (μ + z)) := hΦc.comp (by fun_prop)
  simp only [resamplingInterpolation, sub_zero, Real.sqrt_zero, Real.sqrt_one]
  change (∫ q, Φ (resamplingAffinePoint μ 0 1 (resamplingTripleOriginal q.1) q.2) ∂P.prod γ) = _
  simpa only [Function.comp_apply, resamplingAffinePoint, zero_smul, one_smul, add_zero] using
    (measurePreserving_snd (μ := P) (ν := γ)).hasLaw.integral_comp
      hf0.aestronglyMeasurable

omit [DecidableEq ι] [MeasurableSingletonClass ι] [DecidableEq κ] [CompleteSpace K] in
/-- At time one the actual interpolation is precisely the original sum law.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem resamplingInterpolation_one
    (ν : ι → Measure (κ → ℝ)) [∀ i, IsProbabilityMeasure (ν i)]
    (γ : Measure (κ → ℝ)) [IsProbabilityMeasure γ]
    (Φ : (κ → ℝ) → K) (hΦc : Continuous Φ) :
    resamplingInterpolation ν γ Φ 1 =
      ∫ p, Φ (resamplingTripleOriginal p) ∂resamplingTripleMeasure ν := by
  let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
  let P := resamplingTripleMeasure ν
  simp only [resamplingInterpolation, sub_self, Real.sqrt_one, Real.sqrt_zero]
  change (∫ q, Φ (resamplingAffinePoint μ 1 0 (resamplingTripleOriginal q.1) q.2) ∂P.prod γ) = _
  have hp (q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ)) :
      resamplingAffinePoint μ 1 0 (resamplingTripleOriginal q.1) q.2 =
        resamplingTripleOriginal q.1 := by
    simp only [resamplingAffinePoint, one_smul, zero_smul, add_zero]
    abel
  simp_rw [hp]
  have hXm : Measurable (resamplingTripleOriginal : ι × ((ι × Fin 3) → κ → ℝ) → κ → ℝ) := by
    unfold resamplingTripleOriginal
    fun_prop
  exact (measurePreserving_fst (μ := P) (ν := γ)).hasLaw.integral_comp
    (hΦc.comp_aestronglyMeasurable hXm.stronglyMeasurable.aestronglyMeasurable)

/-- The actual interpolation derivative follows from differentiation under the
integral, genuine discrete resampling, and genuine Gaussian integration by
parts. The exact coefficients are `N/(4 sqrt t)` and `N/4`.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem hasDerivAt_resamplingInterpolation
    (ν : ι → Measure (κ → ℝ)) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : (κ → ℝ) → κ → ℝ) 2 (ν i))
    (γ : Measure (κ → ℝ)) (hγ : HasGaussianLaw (id : (κ → ℝ) → κ → ℝ) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : κ → ℝ => z i), (fun z : κ → ℝ => z j); γ] =
        cov[(fun p : ι × ((ι × Fin 3) → κ → ℝ) => resamplingTripleOriginal p i),
          (fun p : ι × ((ι × Fin 3) → κ → ℝ) => resamplingTripleOriginal p j);
          resamplingTripleMeasure ν])
    (Φ : (κ → ℝ) → ℂ) (f : (κ → ℝ) → F) (df : (κ → ℝ) → (κ → ℝ) →L[ℝ] F)
    (B : (κ → ℝ) →L[ℝ] F →L[ℝ] ℂ)
    (hΦ : ∀ y, HasFDerivAt Φ (B.flip (f y)) y)
    (hf : ∀ y, HasFDerivAt f (df y) y) (hdf : Continuous df)
    (CΦ C C' : ℝ) (hΦb : ∀ y, ‖Φ y‖ ≤ CΦ)
    (hfb : ∀ y, ‖f y‖ ≤ C) (hdfb : ∀ y, ‖df y‖ ≤ C')
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
    let a := Real.sqrt t
    let b := Real.sqrt (1 - t)
    HasDerivAt (resamplingInterpolation ν γ Φ)
      (((Fintype.card ι : ℝ) / (4 * a)) •
          (∫ q, B (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
            (f (resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2) -
              f (resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2))
            ∂(resamplingTripleMeasure ν).prod γ) -
        ((Fintype.card ι : ℝ) / 4) •
          ∫ q, B (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
            (df (resamplingAffinePoint μ a b (resamplingTripleSecond q.1) q.2)
              (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1))
            ∂(resamplingTripleMeasure ν).prod γ) t := by
  have := hγ.isProbabilityMeasure
  dsimp only
  let μ := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure ν
  let P := resamplingTripleMeasure ν
  let a := Real.sqrt t
  let b := Real.sqrt (1 - t)
  let Y := fun q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ) =>
    resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2
  let DΦ : (κ → ℝ) → (κ → ℝ) →L[ℝ] ℂ := fun y => B.flip (f y)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun y => (hf y).continuousAt)
  have hDΦc : Continuous DΦ := B.flip.continuous.comp hfc
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hfb 0)
  have hDΦb (y : κ → ℝ) : ‖DΦ y‖ ≤ ‖B.flip‖ * C :=
    (B.flip.le_opNorm (f y)).trans (mul_le_mul_of_nonneg_left (hfb y) (norm_nonneg _))
  have hX := ((memLp_resamplingTriple_sums ν hν).1.integrable one_le_two).comp_fst γ
  have hXc := hX.sub (integrable_const μ)
  have hZi : Integrable
      (fun q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ) => q.2) (P.prod γ) :=
    (hγ.memLp_two.integrable one_le_two).comp_snd P
  have hd := hasDerivAt_integral_sqrt_affine_path _ _ hXc hZi μ Φ DΦ hΦ hDΦc
    CΦ (‖B.flip‖ * C) (mul_nonneg (norm_nonneg B.flip) hC0) hΦb hDΦb ht ht1
  have hLi := (integrable_bilin_resamplingAffine ν hν γ a b f hfc C hfb B).1
  have hXm : AEMeasurable (resamplingTripleOriginal : ι × ((ι × Fin 3) → κ → ℝ) → κ → ℝ) P :=
    (memLp_resamplingTriple_sums ν hν).1.aestronglyMeasurable.aemeasurable
  have hGi := (integrable_bilin_gaussian_affine_product P resamplingTripleOriginal hXm γ hγ μ a b
    f hfc df hdf C C' hfb hdfb B).1
  have hform : (∫ q, DΦ (Y q)
        ((1 / (2 * a)) • (resamplingTripleOriginal q.1 - μ) -
          (1 / (2 * b)) • q.2) ∂P.prod γ) =
      (1 / (2 * a)) • (∫ q, B (resamplingTripleOriginal q.1 - μ) (f (Y q)) ∂P.prod γ) -
        (1 / (2 * b)) • (∫ q, B q.2 (f (Y q)) ∂P.prod γ) := by
    have hp (q : (ι × ((ι × Fin 3) → κ → ℝ)) × (κ → ℝ)) :
        DΦ (Y q) ((1 / (2 * a)) • (resamplingTripleOriginal q.1 - μ) -
          (1 / (2 * b)) • q.2) =
        (1 / (2 * a)) • B (resamplingTripleOriginal q.1 - μ) (f (Y q)) -
          (1 / (2 * b)) • B q.2 (f (Y q)) := by simp [DΦ]
    simp_rw [hp]
    have hLs : Integrable (fun q => (1 / (2 * a)) •
        B (resamplingTripleOriginal q.1 - μ) (f (Y q))) (P.prod γ) := by
      refine (hLi.smul (1 / (2 * a))).congr ?_
      filter_upwards [] with q
      rfl
    have hGs : Integrable (fun q => (1 / (2 * b)) • B q.2 (f (Y q))) (P.prod γ) := by
      refine (hGi.smul (1 / (2 * b))).congr ?_
      filter_upwards [] with q
      rfl
    rw [integral_sub hLs hGs, integral_smul, integral_smul]
  have hfirst := integral_bilin_resamplingStein_first ν hν γ a b f hfc C hfb B
  have hsecond := integral_bilin_resamplingStein_gaussian ν hν γ hγ hmean hcov a b f df hf hdf
    C C' hfb hdfb B
  have ha0 : a ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hb0 : b ≠ 0 := (Real.sqrt_pos.mpr (by linarith : 0 < 1 - t)).ne'
  have hfacA : (1 / (2 * a)) * ((Fintype.card ι : ℝ) / 2) =
      (Fintype.card ι : ℝ) / (4 * a) := by field_simp; ring
  have hfacB : (1 / (2 * b)) * (b * (Fintype.card ι : ℝ) / 2) =
      (Fintype.card ι : ℝ) / 4 := by field_simp; ring
  change HasDerivAt (resamplingInterpolation ν γ Φ)
    (∫ q, DΦ (Y q) ((1 / (2 * a)) • (resamplingTripleOriginal q.1 - μ) -
      (1 / (2 * b)) • q.2) ∂P.prod γ) t at hd
  apply hd.congr_deriv
  rw [hform, hfirst, hsecond, smul_smul, smul_smul, hfacA, hfacB]

end NLAlib
