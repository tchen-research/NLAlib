import NLAlib.Probability.Rademacher.EmpiricalProcess
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Complex empirical square suprema

Real and imaginary parts reduce the actual squared complex modulus to the
checked real empirical-process estimate. All expectations use the given
coordinate laws. The parameter class need not be countable.

This supplies a variance-proxy estimate for independent-sum spectral
universality (arXiv:2201.05142v3, proof of Lemma 5.8), rather than assuming that estimate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical

namespace NLAlib

variable {ι T Ω : Type*} [Fintype ι] [Nonempty T]
    [TopologicalSpace Ω] [SecondCountableTopology Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]

/-- Bounded continuous complex tests have an integrable squared supremum
under the literal finite product of their coordinate laws. -/
theorem integrable_ciSup_sum_norm_sq_of_continuous
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (X : ι → Ω → T → ℂ) (hXc : ∀ i t, Continuous (fun ω => X i ω t))
    {R : ℝ} (hR : 0 ≤ R) (hX : ∀ i ω t, ‖X i ω t‖ ≤ R) :
    Integrable (fun x : ι → Ω => ⨆ t, ∑ i, ‖X i (x i) t‖ ^ 2) (Measure.pi ν) := by
  apply integrable_ciSup_of_continuous_of_abs_le (Measure.pi ν)
    (fun x t => ∑ i, ‖X i (x i) t‖ ^ 2)
  · intro t
    exact continuous_finsetSum _ fun i _ =>
      ((hXc i t).comp (continuous_apply i)).norm.pow 2
  · intro x t
    rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_le_sum fun i _ =>
      (sq_le_sq₀ (norm_nonneg _) hR).mpr (hX i (x i) t)

/-- Actual bounded centered complex tests in a sign-closed class satisfy
the square-supremum estimate with coefficient `16 * R`. No expectation
comparison is supplied as a premise. -/
theorem integral_ciSup_sum_norm_sq_le_mean_add_sixteen_mul_of_centered
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (X : ι → Ω → T → ℂ) (hXc : ∀ i t, Continuous (fun ω => X i ω t))
    {R v : ℝ} (hR : 0 ≤ R) (hX : ∀ i ω t, ‖X i ω t‖ ≤ R)
    (hmean : ∀ i t, ∫ ω, X i ω t ∂ν i = 0)
    (hneg : ∀ t, ∃ u, ∀ i ω, X i ω u = -X i ω t)
    (hvariance : ∀ t, (∑ i, ∫ ω, ‖X i ω t‖ ^ 2 ∂ν i) ≤ v) :
    (∫ x : ι → Ω, ⨆ t, ∑ i, ‖X i (x i) t‖ ^ 2 ∂Measure.pi ν) ≤
      2 * v + 16 * R *
        ∫ x : ι → Ω, ⨆ t, ‖∑ i, X i (x i) t‖ ∂Measure.pi ν := by
  let μ := Measure.pi ν
  let Y (k : Bool) (i : ι) (ω : Ω) (t : T) : ℝ :=
    if k then (X i ω t).re else (X i ω t).im
  have hYc (k : Bool) (i : ι) (t : T) : Continuous (fun ω => Y k i ω t) := by
    cases k <;> simp only [Y, Bool.false_eq_true, ↓reduceIte]
    · exact Complex.continuous_im.comp (hXc i t)
    · exact Complex.continuous_re.comp (hXc i t)
  have hY (k : Bool) (i : ι) (ω : Ω) (t : T) : |Y k i ω t| ≤ R := by
    cases k
    · exact (Complex.abs_im_le_norm _).trans (hX i ω t)
    · exact (Complex.abs_re_le_norm _).trans (hX i ω t)
  have hXi (i : ι) (t : T) : Integrable (fun ω => X i ω t) (ν i) :=
    Integrable.of_bound (hXc i t).measurable.aestronglyMeasurable R
      (ae_of_all _ fun ω => hX i ω t)
  have hYi (k : Bool) (i : ι) (t : T) : Integrable (fun ω => Y k i ω t ^ 2) (ν i) := by
    apply Integrable.of_bound ((hYc k i t).pow 2).measurable.aestronglyMeasurable (R ^ 2)
    apply ae_of_all
    intro ω
    change ‖Y k i ω t ^ 2‖ ≤ R ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hY k i ω t)
  have hXsq (i : ι) (t : T) : Integrable (fun ω => ‖X i ω t‖ ^ 2) (ν i) := by
    apply Integrable.of_bound ((hXc i t).norm.pow 2).measurable.aestronglyMeasurable (R ^ 2)
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hR).mpr (hX i ω t)
  have hYm (k : Bool) (i : ι) (t : T) : ∫ ω, Y k i ω t ∂ν i = 0 := by
    cases k
    · change (∫ ω, (X i ω t).im ∂ν i) = 0
      simpa using Complex.imCLM.integral_comp_comm (hXi i t) |>.trans
        (congrArg Complex.imCLM (hmean i t))
    · change (∫ ω, (X i ω t).re ∂ν i) = 0
      simpa using Complex.reCLM.integral_comp_comm (hXi i t) |>.trans
        (congrArg Complex.reCLM (hmean i t))
  have hYn (k : Bool) (t : T) : ∃ u, ∀ i ω, Y k i ω u = -Y k i ω t := by
    obtain ⟨u, hu⟩ := hneg t
    refine ⟨u, fun i ω => ?_⟩
    cases k <;> simp [Y, hu]
  have hYv (k : Bool) (t : T) : (∑ i, ∫ ω, Y k i ω t ^ 2 ∂ν i) ≤ v := by
    apply le_trans (Finset.sum_le_sum fun i _ => integral_mono (hYi k i t) (hXsq i t) ?_)
      (hvariance t)
    intro ω
    cases k
    · have h := Complex.sq_norm_sub_sq_im (X i ω t)
      change (X i ω t).im ^ 2 ≤ ‖X i ω t‖ ^ 2
      nlinarith [sq_nonneg (X i ω t).re]
    · have h := Complex.sq_norm_sub_sq_re (X i ω t)
      change (X i ω t).re ^ 2 ≤ ‖X i ω t‖ ^ 2
      nlinarith [sq_nonneg (X i ω t).im]
  have hnorm (x : ι → Ω) (t : T) : ‖∑ i, X i (x i) t‖ ≤ ∑ _i : ι, R :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hX i (x i) t)
  have hN : Integrable (fun x : ι → Ω => ⨆ t, ‖∑ i, X i (x i) t‖) μ := by
    apply integrable_ciSup_of_continuous_of_abs_le μ
      (fun x t => ‖∑ i, X i (x i) t‖)
    · intro t
      exact (continuous_finsetSum _ fun i _ => (hXc i t).comp (continuous_apply i)).norm
    · intro x t
      simpa only [abs_of_nonneg (norm_nonneg _)] using hnorm x t
  have hL (k : Bool) : Integrable (fun x : ι → Ω => ⨆ t, ∑ i, Y k i (x i) t) μ := by
    apply integrable_ciSup_of_continuous_of_abs_le μ
      (fun x t => ∑ i, Y k i (x i) t)
    · intro t
      exact continuous_finsetSum _ fun i _ => (hYc k i t).comp (continuous_apply i)
    · intro x t
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => hY k i (x i) t)
  have hQ (k : Bool) : Integrable (fun x : ι → Ω => ⨆ t, ∑ i, Y k i (x i) t ^ 2) μ := by
    apply integrable_ciSup_of_continuous_of_abs_le μ
      (fun x t => ∑ i, Y k i (x i) t ^ 2)
    · intro t
      exact continuous_finsetSum _ fun i _ => ((hYc k i t).comp (continuous_apply i)).pow 2
    · intro x t
      rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      exact Finset.sum_le_sum fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hY k i (x i) t)
  have hbQ (k : Bool) (x : ι → Ω) : BddAbove (Set.range fun t => ∑ i, Y k i (x i) t ^ 2) := by
    refine ⟨∑ _i : ι, R ^ 2, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact Finset.sum_le_sum fun i _ => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hY k i (x i) t)
  have hleL (k : Bool) :
      (∫ x, ⨆ t, ∑ i, Y k i (x i) t ∂μ) ≤ ∫ x, ⨆ t, ‖∑ i, X i (x i) t‖ ∂μ := by
    apply integral_mono (hL k) hN
    intro x
    apply ciSup_le
    intro t
    apply le_trans (b := ‖∑ i, X i (x i) t‖)
    · cases k
      · simpa [Y, Complex.im_sum] using Complex.im_le_norm (∑ i, X i (x i) t)
      · simpa [Y, Complex.re_sum] using Complex.re_le_norm (∑ i, X i (x i) t)
    · exact le_ciSup ⟨∑ _i : ι, R, by rintro _ ⟨u, rfl⟩; exact hnorm x u⟩ t
  have hbound (k : Bool) : (∫ x, ⨆ t, ∑ i, Y k i (x i) t ^ 2 ∂μ) ≤
      v + 8 * R * ∫ x, ⨆ t, ‖∑ i, X i (x i) t‖ ∂μ := by
    have h := integral_ciSup_sum_sq_le_mean_add_eight_mul_of_centered ν
      (Y k) (hYc k) hR (hY k) (hYm k) (hYn k) (hYv k)
    change (∫ x, ⨆ t, ∑ i, Y k i (x i) t ^ 2 ∂μ) ≤
      v + 8 * R * ∫ x, ⨆ t, ∑ i, Y k i (x i) t ∂μ at h
    nlinarith [hleL k]
  have hsplit := integral_mono
    (integrable_ciSup_sum_norm_sq_of_continuous ν X hXc hR hX)
    ((hQ true).add (hQ false)) (fun x => ?_)
  · change (∫ x, ⨆ t, ∑ i, ‖X i (x i) t‖ ^ 2 ∂μ) ≤
      ∫ x, (⨆ t, ∑ i, Y true i (x i) t ^ 2) +
        (⨆ t, ∑ i, Y false i (x i) t ^ 2) ∂μ at hsplit
    rw [integral_add (hQ true) (hQ false)] at hsplit
    linarith [hbound true, hbound false]
  · apply ciSup_le
    intro t
    calc
      (∑ i, ‖X i (x i) t‖ ^ 2) =
          (∑ i, Y true i (x i) t ^ 2) + ∑ i, Y false i (x i) t ^ 2 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have h := Complex.sq_norm_sub_sq_re (X i (x i) t)
        change ‖X i (x i) t‖ ^ 2 = (X i (x i) t).re ^ 2 + (X i (x i) t).im ^ 2
        linarith
      _ ≤ _ := add_le_add (le_ciSup (hbQ true x) t) (le_ciSup (hbQ false x) t)

end NLAlib
