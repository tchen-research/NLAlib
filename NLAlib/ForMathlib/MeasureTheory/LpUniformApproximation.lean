import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Uniform approximation controls real Lp norms on probability spaces

The actual real Lp norm is stable under a pointwise uniform perturbation.
This small scalar lemma is used with the constructed spectral probability
measure in the free-resolvent Jackson argument.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A uniform approximation error bounds the increase in the actual real
Lp norm on a probability space. Only the comparison function needs Lp membership. -/
theorem MeasureTheory.lpNorm_le_add_of_uniform_approximation {f g : Ω → ℝ}
    {p : ENNReal} (hg : MemLp g p μ) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {δ : ℝ} (hδ : 0 ≤ δ) (hfg : ∀ x, |f x - g x| ≤ δ) :
    lpNorm f p μ ≤ lpNorm g p μ + δ := by
  have hp_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have herror : lpNorm (f - g) p μ ≤ δ := by
    have h := lpNorm_mono_real (memLp_const δ : MemLp (fun _ : Ω => δ) p μ)
      (f := f - g) (fun x => by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hfg x)
    simpa only [lpNorm_const' hp_zero hp_top, probReal_univ, Real.one_rpow,
      mul_one, Real.norm_eq_abs, abs_of_nonneg hδ] using h
  exact (lpNorm_le_lpNorm_add_lpNorm_sub' hg hp).trans (add_le_add le_rfl herror)

end
