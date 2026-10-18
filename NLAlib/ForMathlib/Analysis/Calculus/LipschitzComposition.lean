import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Derivatives of Lipschitz compositions

A differentiable inner curve transfers its pointwise speed bound through a
Lipschitz outer function. The outer function need not be differentiable.
-/

noncomputable section

open Filter Set
open scoped Topology

/-- A Lipschitz outer function bounds the derivative of its composition with a
real differentiable curve, even if the outer function has no derivative there.
The total derivative is zero when the composition is not differentiable. -/
theorem LipschitzOnWith.norm_deriv_comp_le {f g : ℝ → ℝ} {s : Set ℝ} {L : NNReal} {x : ℝ}
    (hf : LipschitzOnWith L f s) (hg : DifferentiableAt ℝ g x)
    (hgs : ∀ᶠ y in 𝓝 x, g y ∈ s) :
    ‖deriv (f ∘ g) x‖ ≤ L * ‖deriv g x‖ := by
  by_cases hd : DifferentiableAt ℝ (f ∘ g) x
  · apply le_of_tendsto_of_tendsto hd.hasDerivAt.tendsto_slope.norm
      (tendsto_const_nhds.mul hg.hasDerivAt.tendsto_slope.norm)
    filter_upwards [hgs.filter_mono nhdsWithin_le_nhds] with y hy
    simp only [slope, vsub_eq_sub, norm_smul, norm_inv, Real.norm_eq_abs]
    have hx : g x ∈ s := show x ∈ {y | g y ∈ s} from mem_of_mem_nhds hgs
    have hb := hf.norm_sub_le hy hx
    simp only [Real.norm_eq_abs] at hb
    dsimp only [Function.comp_apply]
    nlinarith [mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg (y - x)))]
  · rw [deriv_zero_of_not_differentiableAt hd, norm_zero]
    positivity
