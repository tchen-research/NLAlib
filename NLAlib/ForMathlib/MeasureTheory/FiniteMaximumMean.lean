import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Means of finite maxima

A finite maximum is bounded by a common bound on its means plus the sum of
its mean absolute deviations. No independence is needed; summably small
deviations therefore give bounds uniform in the number of variables.
-/

noncomputable section

namespace MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
  {μ : Measure Ω}

/-- A finite supremum of integrable real functions is integrable. -/
theorem integrable_iSup_of_integrable_finite (f : ι → Ω → ℝ)
    (hf : ∀ i, Integrable (f i) μ) : Integrable (fun ω => ⨆ i, f i ω) μ := by
  classical
  apply (integrable_finsetSum Finset.univ fun i _ => (hf i).abs).mono'
    (AEMeasurable.iSup fun i => (hf i).aemeasurable).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => f i ω)
  rw [← hi, Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (f j ω)) (Finset.mem_univ i)

/-- A finite maximum has mean at most a common mean bound plus the sum of
the mean absolute deviations. The variables may be arbitrarily dependent. -/
theorem integral_iSup_le_mean_add_sum_integral_abs_sub
    [IsProbabilityMeasure μ] (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ)
    {M : ℝ} (hM : ∀ i, ∫ ω, f i ω ∂μ ≤ M) :
    (∫ ω, ⨆ i, f i ω ∂μ) ≤
      M + ∑ i, ∫ ω, |f i ω - ∫ x, f i x ∂μ| ∂μ := by
  classical
  have hd (i : ι) : Integrable (fun ω => |f i ω - ∫ x, f i x ∂μ|) μ :=
    ((hf i).sub (integrable_const _)).abs
  calc
    _ ≤ ∫ ω, M + ∑ i, |f i ω - ∫ x, f i x ∂μ| ∂μ := by
      apply integral_mono (integrable_iSup_of_integrable_finite f hf)
        ((integrable_const _).add (integrable_finsetSum Finset.univ fun i _ => hd i))
      intro ω
      apply ciSup_le
      intro i
      change f i ω ≤ M + ∑ j, |f j ω - ∫ x, f j x ∂μ|
      have hsingle := Finset.single_le_sum
        (fun j _ => abs_nonneg (f j ω - ∫ x, f j x ∂μ)) (Finset.mem_univ i)
      have habs := le_abs_self (f i ω - ∫ x, f i x ∂μ)
      linarith [hM i]
    _ = _ := by
      rw [integral_add (integrable_const _) (integrable_finsetSum _ fun i _ => hd i),
        integral_finsetSum _ fun i _ => hd i]
      simp

end MeasureTheory
