import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cauchy–Schwarz for square roots of integrable nonnegative functions

The square-root product envelope used to integrate spectral moment interpolation is controlled
by the geometric mean of the corresponding integrals.
-/

noncomputable section

namespace MeasureTheory

/-- The product of square roots of two nonnegative integrable functions is integrable. -/
theorem Integrable.sqrt_mul_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    Integrable (fun ω => Real.sqrt (f ω) * Real.sqrt (g ω)) μ := by
  have hfs : MemLp (fun ω => Real.sqrt (f ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).2
    simpa only [Real.sq_sqrt (hf0 _)] using hf
  have hgs : MemLp (fun ω => Real.sqrt (g ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable)).2
    simpa only [Real.sq_sqrt (hg0 _)] using hg
  exact hfs.integrable_mul hgs

/-- Cauchy–Schwarz bounds an integral of a square-root product by the square root of the
product of its two integrals. -/
theorem integral_sqrt_mul_sqrt_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    (∫ ω, Real.sqrt (f ω) * Real.sqrt (g ω) ∂μ) ≤
      Real.sqrt ((∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ) := by
  have hfs : MemLp (fun ω => Real.sqrt (f ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).2
    simpa only [Real.sq_sqrt (hf0 _)] using hf
  have hgs : MemLp (fun ω => Real.sqrt (g ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable)).2
    simpa only [Real.sq_sqrt (hg0 _)] using hg
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 from Real.holderConjugate_iff.mpr
      ⟨by norm_num, by norm_num⟩)
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg (f ω))
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg (g ω))
    (by simpa using hfs) (by simpa using hgs)
  simp_rw [Real.rpow_two, Real.sq_sqrt (hf0 _), Real.sq_sqrt (hg0 _)] at hcs
  rw [Real.sqrt_mul (integral_nonneg hf0)]
  simpa only [Real.sqrt_eq_rpow, one_div] using hcs

end MeasureTheory
