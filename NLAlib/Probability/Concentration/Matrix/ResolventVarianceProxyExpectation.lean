import NLAlib.Probability.Concentration.Matrix.BilinearCopyExpectation
import NLAlib.Probability.Concentration.Matrix.IndependentSquareSum
import NLAlib.Probability.Moments.SquareMass
import NLAlib.Matrix.Norms.MatrixVarianceProxy

/-!
# Expectation of the actual resolvent variance proxy

The literal original/copy proxy is controlled by the native bilinear
second-moment budget, the expectation of the actual centered sum norm,
and the actual matrix variance. No proxy-expectation estimate is assumed.

Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemmas 5.8--5.9.
This is a concentration prerequisite for independent-sum spectrum
universality; the probabilistic spectral inclusions are separate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical Matrix.Norms.L2Operator

namespace NLAlib

variable {ι n Ω : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [MeasurableSpace Ω]

/-- A source-scale expectation bound for the computed resolvent variance
proxy of actual bounded centered independent Hermitian summands. Native
matrix variance and actual unit-ball bilinear moments are retained.
atlas: independent-sum-spectrum-universality (partial) -/
theorem integrable_and_integral_resolventVarianceProxy_copy_pi_le
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R v η : ℝ} (hR : 0 ≤ R) (hη : 0 < η)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i = 0)
    (hvariance : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ ω, ‖star a.ofLp ⬝ᵥ (Z i ω *ᵥ b.ofLp)‖ ^ 2 ∂ν i) ≤ v) :
    Integrable (fun q : (ι → Ω) × (ι → Ω) =>
      resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R η)
        ((Measure.pi ν).prod (Measure.pi ν)) ∧
      (∫ q : (ι → Ω) × (ι → Ω),
        resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R η
          ∂((Measure.pi ν).prod (Measure.pi ν))) ≤
        (2 / η ^ 4) * (8 * v + 64 * R *
          ∫ x : ι → Ω, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν) +
        (32 * R ^ 2 / η ^ 6) * ((Real.exp 1 - 1) *
          specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂ν i) + R ^ 2 * Real.log (Fintype.card n)) := by
  let μ := Measure.pi ν
  let Y (i : ι) (x : ι → Ω) := Z i (x i)
  let D (q : (ι → Ω) × (ι → Ω)) (i : ι) := Y i q.1 - Y i q.2
  have hYm (i : ι) : Measurable (Y i) := (hZm i).comp (measurable_pi_apply i)
  have hYH (i : ι) : ∀ᵐ x ∂μ, (Y i x).IsHermitian :=
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hZH i)
  have hYB (i : ι) : ∀ᵐ x ∂μ, specNorm (Y i x) ≤ R :=
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hZ i)
  have hDH : ∀ᵐ q ∂μ.prod μ, ∀ i, (D q i).IsHermitian := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.mpr hYH),
      Measure.quasiMeasurePreserving_snd.ae (ae_all_iff.mpr hYH)] with q h₁ h₂
    exact fun i => (h₁ i).sub (h₂ i)
  have hBC := integrable_and_integral_bilinearSquareMass_copy_sub_le μ Y hYm hR hYB
  have hGC := integrable_and_integral_specNorm_sum_sub_sq_prod_le μ Y hYm hR hYH hYB
  have hgram : (fun q => specNorm (∑ i, (D q i)ᴴ * D q i)) =ᵐ[μ.prod μ]
      (fun q => specNorm (∑ i, D q i ^ 2)) := by
    filter_upwards [hDH] with q hq
    simp only [(hq _).eq, pow_two]
  have hGi : Integrable (fun q => specNorm (∑ i, (D q i)ᴴ * D q i)) (μ.prod μ) :=
    hGC.1.congr hgram.symm
  have hWi : Integrable (fun q => resolventVarianceProxy (D q) Finset.univ R η) (μ.prod μ) := by
    convert (hBC.1.const_mul (2 / η ^ 4)).add (hGi.const_mul (8 * R ^ 2 / η ^ 6)) using 1 <;>
      rfl
  refine ⟨hWi, ?_⟩
  have hSquare := integrable_and_integral_specNorm_sum_sq_le_chernoff μ Y hR hYm
    (iIndepFun_pi fun i => (hZm i).aemeasurable) hYH hYB
  have hSecond : (∑ i, ∫ x, Y i x ^ 2 ∂μ) = ∑ i, ∫ ω, Z i ω ^ 2 ∂ν i := by
    apply Finset.sum_congr rfl
    intro i _
    have hm : AEStronglyMeasurable (fun ω => Z i ω ^ 2) (ν i) := by
      simpa only [pow_two] using ((hZm i).matrix_mul (hZm i)).aestronglyMeasurable
    exact (measurePreserving_eval ν i).hasLaw.integral_comp hm
  rw [hSecond] at hSquare
  have hBbound := integral_bilinearSquareMass_copy_sub_pi_le ν Z hZm hR hZ hmean hvariance
  have hGbound : (∫ q, specNorm (∑ i, (D q i)ᴴ * D q i) ∂μ.prod μ) ≤
      4 * ((Real.exp 1 - 1) * specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂ν i) +
        R ^ 2 * Real.log (Fintype.card n)) := by
    rw [integral_congr_ae hgram]
    exact hGC.2.trans (mul_le_mul_of_nonneg_left hSquare.2 (by norm_num))
  change (∫ q, resolventVarianceProxy (D q) Finset.univ R η ∂μ.prod μ) ≤ _
  simp only [resolventVarianceProxy, matrixVarianceProxy]
  rw [integral_add (hBC.1.const_mul _) (hGi.const_mul _), integral_const_mul, integral_const_mul]
  calc
    _ ≤ (2 / η ^ 4) * (8 * v + 64 * R *
          ∫ x : ι → Ω, specNorm (∑ i, Z i (x i)) ∂μ) +
        (8 * R ^ 2 / η ^ 6) * (4 * ((Real.exp 1 - 1) *
          specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂ν i) + R ^ 2 * Real.log (Fintype.card n))) :=
      add_le_add (mul_le_mul_of_nonneg_left hBbound (by positivity))
        (mul_le_mul_of_nonneg_left hGbound (by positivity))
    _ = _ := by ring

end NLAlib
