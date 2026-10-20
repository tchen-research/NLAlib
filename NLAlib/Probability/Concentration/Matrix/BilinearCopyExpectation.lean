import NLAlib.Probability.Concentration.Matrix.BilinearSquareExpectation

/-!
# Bilinear square energy of actual independent copies

The product sample copies the full matrix array. The deterministic
square-energy difference bound controls its expectation; no independence
among the original coordinates is needed for the copy bound itself.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Classical Matrix.Norms.L2Operator

namespace NLAlib

variable {ι n Ω : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [MeasurableSpace Ω]

/-- Almost-everywhere spectral boundedness derives integrability of the
actual bilinear square mass, even for empty labels and matrix dimension. -/
theorem integrable_bilinearSquareMass_of_ae_bound
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R : ℝ} (hR : 0 ≤ R) (hZ : ∀ i, ∀ᵐ ω ∂μ, specNorm (Z i ω) ≤ R) :
    Integrable (fun ω => bilinearSquareMass (fun i => Z i ω) Finset.univ) μ := by
  have hm := (measurable_bilinearSquareMass (n := n) (ι := ι) Finset.univ).comp
    (measurable_pi_lambda _ hZm)
  apply Integrable.of_bound hm.aestronglyMeasurable ((Fintype.card ι : ℝ) * R ^ 2)
  filter_upwards [ae_all_iff.mpr hZ] with ω hω
  change ‖bilinearSquareMass (fun i => Z i ω) Finset.univ‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (bilinearSquareMass_nonneg _ _)]
  calc
    _ ≤ ∑ i, specNorm (Z i ω) ^ 2 := by
      simpa using bilinearSquareMass_le_sum_specNorm_sq (fun i => Z i ω) Finset.univ
    _ ≤ ∑ _i : ι, R ^ 2 := Finset.sum_le_sum fun i _ =>
      (sq_le_sq₀ (specNorm_nonneg _) hR).mpr (hω i)
    _ = _ := by simp

/-- The actual difference of two copies has expected bilinear square mass
at most four times the original expectation. Both integrability statements
are derived from the actual almost-everywhere spectral bound. -/
theorem integrable_and_integral_bilinearSquareMass_copy_sub_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R : ℝ} (hR : 0 ≤ R) (hZ : ∀ i, ∀ᵐ ω ∂μ, specNorm (Z i ω) ≤ R) :
    Integrable (fun q : Ω × Ω =>
      bilinearSquareMass (fun i => Z i q.1 - Z i q.2) Finset.univ) (μ.prod μ) ∧
      (∫ q : Ω × Ω, bilinearSquareMass (fun i => Z i q.1 - Z i q.2) Finset.univ ∂μ.prod μ) ≤
        4 * ∫ ω, bilinearSquareMass (fun i => Z i ω) Finset.univ ∂μ := by
  have hBi := integrable_bilinearSquareMass_of_ae_bound μ Z hZm hR hZ
  have hDm (i : ι) : Measurable (fun q : Ω × Ω => Z i q.1 - Z i q.2) :=
    ((hZm i).comp measurable_fst).sub ((hZm i).comp measurable_snd)
  have hDB (i : ι) : ∀ᵐ q : Ω × Ω ∂μ.prod μ, specNorm (Z i q.1 - Z i q.2) ≤ 2 * R := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hZ i),
      Measure.quasiMeasurePreserving_snd.ae (hZ i)] with q h₁ h₂
    change ‖Z i q.1‖ ≤ R at h₁
    change ‖Z i q.2‖ ≤ R at h₂
    exact (norm_sub_le _ _).trans (by linarith)
  have hDi := integrable_bilinearSquareMass_of_ae_bound (μ.prod μ)
    (fun i q => Z i q.1 - Z i q.2) hDm (by positivity : 0 ≤ 2 * R) hDB
  refine ⟨hDi, ?_⟩
  have h := integral_mono hDi (((hBi.comp_fst μ).const_mul 2).add ((hBi.comp_snd μ).const_mul 2))
    (fun q => bilinearSquareMass_sub_le (fun i => Z i q.1) (fun i => Z i q.2) Finset.univ)
  change (∫ q : Ω × Ω, bilinearSquareMass (fun i => Z i q.1 - Z i q.2) Finset.univ ∂μ.prod μ) ≤
    ∫ q : Ω × Ω, 2 * bilinearSquareMass (fun i => Z i q.1) Finset.univ +
      2 * bilinearSquareMass (fun i => Z i q.2) Finset.univ ∂μ.prod μ at h
  rw [integral_add ((hBi.comp_fst μ).const_mul 2) ((hBi.comp_snd μ).const_mul 2),
    integral_const_mul, integral_const_mul] at h
  have hf : (∫ q : Ω × Ω, bilinearSquareMass (fun i => Z i q.1) Finset.univ ∂μ.prod μ) =
      ∫ ω, bilinearSquareMass (fun i => Z i ω) Finset.univ ∂μ := by
    simpa only [probReal_univ, one_smul] using
      integral_fun_fst (μ := μ) (ν := μ) (fun ω => bilinearSquareMass (fun i => Z i ω) Finset.univ)
  have hs : (∫ q : Ω × Ω, bilinearSquareMass (fun i => Z i q.2) Finset.univ ∂μ.prod μ) =
      ∫ ω, bilinearSquareMass (fun i => Z i ω) Finset.univ ∂μ := by
    simpa only [probReal_univ, one_smul] using
      integral_fun_snd (μ := μ) (ν := μ) (fun ω => bilinearSquareMass (fun i => Z i ω) Finset.univ)
  rw [hf, hs] at h
  linarith

/-- Explicit control of the literal original/copy bilinear square energy
for centered independent matrix samples. A native second-moment budget
and actual norm expectation replace an assumed proxy bound.
atlas: independent-sum-spectrum-universality (partial) -/
theorem integral_bilinearSquareMass_copy_sub_pi_le
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R v : ℝ} (hR : 0 ≤ R) (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i = 0)
    (hvariance : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ ω, ‖star a.ofLp ⬝ᵥ (Z i ω *ᵥ b.ofLp)‖ ^ 2 ∂ν i) ≤ v) :
    (∫ q : (ι → Ω) × (ι → Ω),
      bilinearSquareMass (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ
        ∂((Measure.pi ν).prod (Measure.pi ν))) ≤
      8 * v + 64 * R * ∫ x : ι → Ω, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν := by
  have hm (i : ι) : Measurable (fun x : ι → Ω => Z i (x i)) :=
    (hZm i).comp (measurable_pi_apply i)
  have hb (i : ι) : ∀ᵐ x : ι → Ω ∂Measure.pi ν, specNorm (Z i (x i)) ≤ R :=
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hZ i)
  have hcopy := (integrable_and_integral_bilinearSquareMass_copy_sub_le
    (Measure.pi ν) (fun i x => Z i (x i)) hm hR hb).2
  have hbase := integral_bilinearSquareMass_pi_le_of_ae_bound ν Z hZm hR hZ hmean hvariance
  linarith

end NLAlib
