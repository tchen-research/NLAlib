import NLAlib.Probability.Gaussian.Comparison.ResolventMomentInterpolation
import NLAlib.Probability.Moments.ResolventMomentTaylorExpectation
import NLAlib.Probability.Exchangeable.ThirdCopyArrays

/-!
# Actual cubic derivative of the normalized resolvent-moment interpolation

Prerequisite for
`independent-sum-spectrum-universality`. Genuine full-covariance Stein
cancellation and the proved native Taylor kernel give the exact N sqrt(t)/4
coefficient. Matrix support bounds derive every new integrability assertion.

Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Lemma 6.9 and Section 6.4.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
local notation "M" => Matrix n n ℂ
local notation "J" => (n × n) ⊕ (n × n)
local notation "E" => J → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)
local notation "Q" => (ι × ((ι × Fin 3) → E)) × E

open scoped Matrix.Norms.L2Operator in
/-- The derivative of the actual interpolation is the native integrable
cubic kernel expectation. Coordinate-null directions need only the original
second moments; no cubic coordinate integrability premise is imposed. -/
theorem hasDerivAt_resamplingInterpolation_normalizedTrace_mixed_eq_cubicKernel
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : E → E) 2 (ν i))
    (γ : Measure E) (hγ : HasGaussianLaw (id : E → E) γ)
    (hmean : ∀ i, ∫ z, z i ∂γ = 0)
    (hcov : ∀ i j,
      cov[(fun z : E => z i), (fun z : E => z j); γ] =
        cov[(fun q : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal q i),
          (fun q : ι × ((ι × Fin 3) → E) => resamplingTripleOriginal q j);
          resamplingTripleMeasure ν])
    {R : ℝ} (hR : 0 ≤ R) (hBound : ∀ i, ∀ᵐ x ∂ν i, specNorm (L x) ≤ R)
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    let Φ : E → ℂ := fun x => normalizedTrace
      (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)
    let μ := ∫ q, resamplingTripleOriginal q ∂resamplingTripleMeasure ν
    let a := Real.sqrt t
    let b := Real.sqrt (1 - t)
    let K : Q → ℂ := fun q => resolventMomentTaylorKernel A ζ p a
      (resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2)
      (resamplingTripleOriginal q.1 - resamplingTripleFirst q.1)
      (resamplingTripleFirst q.1 - resamplingTripleSecond q.1)
    Integrable K ((resamplingTripleMeasure ν).prod γ) ∧
      HasDerivAt (resamplingInterpolation ν γ Φ)
        (((Fintype.card ι : ℝ) * a / 4) • ∫ q, K q ∂(resamplingTripleMeasure ν).prod γ) t := by
  let := hγ.isProbabilityMeasure
  dsimp only
  let P := (resamplingTripleMeasure ν).prod γ
  let μ := ∫ q, resamplingTripleOriginal q ∂resamplingTripleMeasure ν
  let a := Real.sqrt t
  let b := Real.sqrt (1 - t)
  let Y0 : Q → E := fun q => resamplingAffinePoint μ a b (resamplingTripleOriginal q.1) q.2
  let Y1 : Q → E := fun q => resamplingAffinePoint μ a b (resamplingTripleFirst q.1) q.2
  let Y2 : Q → E := fun q => resamplingAffinePoint μ a b (resamplingTripleSecond q.1) q.2
  let D : Q → E := fun q => resamplingTripleOriginal q.1 - resamplingTripleFirst q.1
  let V : Q → E := fun q => resamplingTripleFirst q.1 - resamplingTripleSecond q.1
  let Φ : E → ℂ := fun x => normalizedTrace
    (resolvent (A + L x) ζ ^ p * resolvent (A + L x) (star ζ) ^ p)
  let f := fderiv ℝ Φ
  let df := fderiv ℝ f
  let B : E →L[ℝ] (E →L[ℝ] ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.id ℝ (E →L[ℝ] ℂ)).flip
  have h01 (q : Q) : Y1 q + a • D q = Y0 q := by
    dsimp only [Y0, Y1, D, resamplingAffinePoint]
    simp only [smul_sub]
    abel
  have h12 (q : Q) : Y1 q - a • V q = Y2 q := by
    dsimp only [Y1, Y2, V, resamplingAffinePoint]
    simp only [smul_sub]
    abel
  have hm := memLp_resamplingTriple_sums ν hν
  have hD2 := (hm.1.sub hm.2.1).comp_fst γ
  have hV2 := (hm.2.1.sub hm.2.2).comp_fst γ
  have hY1m : AEMeasurable Y1 P := by
    have hFirst := hm.2.1.comp_fst γ
    have hZ : AEStronglyMeasurable (fun q : Q => q.2) P :=
      measurable_snd.stronglyMeasurable.aestronglyMeasurable
    exact ((aestronglyMeasurable_const.add
      ((hFirst.aestronglyMeasurable.sub aestronglyMeasurable_const).const_smul a)).add
        (hZ.const_smul b)).aemeasurable
  have hAll : ∀ᵐ q ∂P, ∀ s : Fin 3, ∀ i,
      specNorm (L (q.1.2 (i, s))) ≤ R := by
    rw [ae_all_iff]
    intro s
    have hs := hasLaw_resamplingTriple_prod_full_copy ν γ s
    apply ae_of_ae_map (p := fun z : ι → E => ∀ i, specNorm (L (z i)) ≤ R) hs.aemeasurable
    rw [hs.map_eq, ae_all_iff]
    intro i
    have hi := (measurePreserving_eval ν i).hasLaw
    apply ae_of_ae_map (p := fun z : E => specNorm (L z) ≤ R) hi.aemeasurable
    rw [hi.map_eq]
    exact hBound i
  have hDV : ∀ᵐ q ∂P, specNorm (L (D q)) ≤ 2 * R ∧ specNorm (L (V q)) ≤ 2 * R := by
    filter_upwards [hAll] with q hq
    have hsub (s u : Fin 3) : specNorm (L (q.1.2 (q.1.1, s) - q.1.2 (q.1.1, u))) ≤ 2 * R := by
      rw [map_sub]
      exact (specNorm_sub_le _ _).trans (by linarith [hq s q.1.1, hq u q.1.1])
    constructor
    · simpa only [D, resamplingTriple_difference] using hsub 0 1
    · simpa only [V, resamplingTriple_first_sub_second] using hsub 1 2
  have hTaylor := integrable_and_integral_fderiv_sub_sub_smul_normalizedTrace_mixed_eq_kernel
    P A hA ζ hζ p a Y1 D V hY1m hD2.aestronglyMeasurable.aemeasurable
      hV2.aestronglyMeasurable.aemeasurable (by positivity : 0 ≤ 2 * R) hDV
  have hc : ContDiff ℝ ⊤ Φ := contDiff_normalizedTrace_mixed_resolvent_coordinate A hA ζ hζ p
  have hfc : ContDiff ℝ ⊤ f := hc.fderiv_right (by simp)
  have hdfc : ContDiff ℝ ⊤ df := hfc.fderiv_right (by simp)
  let C1 : ℝ := ((2 * p : ℕ) : ℝ) * |ζ.im|⁻¹ ^ (2 * p + 1) * ‖L‖
  let C2 : ℝ := ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) *
    |ζ.im|⁻¹ ^ (2 * p + 2) * ‖L‖ ^ 2
  have hfb (y : E) : ‖f y‖ ≤ C1 := norm_fderiv_normalizedTrace_mixed_resolvent_coordinate_le A hA ζ hζ p y
  have hdfb (y : E) : ‖df y‖ ≤ C2 := by
    change ‖fderiv ℝ (fderiv ℝ Φ) y‖ ≤ C2
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ Φ), norm_iteratedFDeriv_fderiv]
    exact norm_iteratedFDeriv_two_normalizedTrace_mixed_resolvent_coordinate_le A hA ζ hζ p y
  let I1 : Q → ℂ := fun q => (f (Y0 q) - f (Y1 q)) (D q)
  let I2 : Q → ℂ := fun q => df (Y2 q) (D q) (D q)
  have hI1 : Integrable I1 P := by
    simpa only [I1, B, Y0, Y1, D, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.id_apply] using
      (integrable_bilin_resamplingAffine ν hν γ a b f hfc.continuous C1 hfb B).2
  have hI2 : Integrable I2 P := by
    simpa only [I2, B, Y2, D, resamplingAffinePoint, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.id_apply] using
      integrable_bilin_quadratic_resamplingTriple_affine ν hν γ μ a b df hdfc.continuous C2 hdfb B
  have he : (∫ q, I1 q ∂P) - a • (∫ q, I2 q ∂P) =
      a ^ 2 • ∫ q, resolventMomentTaylorKernel A ζ p a (Y1 q) (D q) (V q) ∂P := by
    have hs := integral_sub hI1 (hI2.smul a)
    simp only [Pi.smul_apply, integral_smul] at hs
    rw [← hs]
    simpa only [Φ, I1, I2, f, df, h01, h12, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] using hTaylor.2.2
  refine ⟨hTaylor.1, ?_⟩
  have hd := hasDerivAt_resamplingInterpolation_normalizedTrace_mixed_resolvent
    ν hν γ hγ hmean hcov A hA ζ hζ p ht ht1
  apply hd.congr_deriv
  change ((Fintype.card ι : ℝ) / (4 * a)) • (∫ q, I1 q ∂P) -
    ((Fintype.card ι : ℝ) / 4) • (∫ q, I2 q ∂P) = _
  have ha : a ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hcoef : ((Fintype.card ι : ℝ) / (4 * a)) * a = (Fintype.card ι : ℝ) / 4 := by
    field_simp
  calc
    _ = ((Fintype.card ι : ℝ) / (4 * a)) • ((∫ q, I1 q ∂P) - a • ∫ q, I2 q ∂P) := by
      rw [smul_sub, smul_smul, hcoef]
    _ = _ := by
      rw [he, smul_smul]
      congr 1
      field_simp
      ring

end NLAlib
