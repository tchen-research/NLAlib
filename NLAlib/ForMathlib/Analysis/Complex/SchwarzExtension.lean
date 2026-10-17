import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Reflecting an upper-half-plane function

The reflection is holomorphic off the real axis when the original function is
holomorphic in the upper half-plane. Values on the real axis are supplied
separately. If an exterior holomorphic function agrees above and satisfies
Schwarz symmetry, the extension agrees with it throughout that exterior domain.
-/

noncomputable section

open Set Filter
open scoped Topology ComplexConjugate

namespace Complex

/-- Reflect an upper-half-plane function below the real axis, retaining the
specified values on the axis itself. No regularity across the axis is implicit. -/
def schwarzHalfPlaneExtension (f axis : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 < z.im then f z else if z.im < 0 then conj (f (conj z)) else axis z

/-- The reflected extension has Schwarz symmetry away from the real axis. -/
theorem schwarzHalfPlaneExtension_conj (f axis : ℂ → ℂ) {z : ℂ}
    (hz : z.im ≠ 0) :
    schwarzHalfPlaneExtension f axis (conj z) =
      conj (schwarzHalfPlaneExtension f axis z) := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · simp [schwarzHalfPlaneExtension, hneg, not_lt_of_ge hneg.le]
  · simp [schwarzHalfPlaneExtension, hpos, not_lt_of_ge hpos.le]

/-- Schwarz-symmetric axis values make the reflected extension symmetric also
at real points. Regularity on the real axis is still a separate property. -/
theorem schwarzHalfPlaneExtension_conj_of_conj_eq_axis (f axis : ℂ → ℂ)
    (haxis : ∀ z : ℂ, axis (conj z) = conj (axis z)) (z : ℂ) :
    schwarzHalfPlaneExtension f axis (conj z) =
      conj (schwarzHalfPlaneExtension f axis z) := by
  by_cases hz : z.im = 0
  · simp [schwarzHalfPlaneExtension, hz, haxis]
  · exact schwarzHalfPlaneExtension_conj f axis hz

/-- Reflection preserves complex differentiability off the real axis. -/
theorem differentiableOn_schwarzHalfPlaneExtension (f axis : ℂ → ℂ)
    (hf : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z) :
    DifferentiableOn ℂ (schwarzHalfPlaneExtension f axis) {z | z.im ≠ 0} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hh : DifferentiableAt ℂ (conj ∘ f ∘ conj) z := by
      simpa only [conj_conj] using (hf (conj z) (by simpa using neg_pos.mpr hneg)).conj_conj
    apply hh.congr_of_eventuallyEq
    filter_upwards [isOpen_lt continuous_im continuous_const |>.mem_nhds hneg] with w hw
    simp only [Function.comp_apply]
    simp [schwarzHalfPlaneExtension, hw, not_lt_of_ge hw.le]
  · apply (hf z hpos).congr_of_eventuallyEq
    filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds hpos] with w hw
    simp [schwarzHalfPlaneExtension, hw]

/-- Exterior agreement above the real axis and Schwarz symmetry determine the
same extension below, while the supplied axis values handle the real points. -/
theorem schwarzHalfPlaneExtension_eq_of_conj_eq
    (f g : ℂ → ℂ) {R : ℝ}
    (hupper : ∀ z : ℂ, R < ‖z‖ → 0 < z.im → f z = g z)
    (href : ∀ z : ℂ, R < ‖z‖ → g (conj z) = conj (g z))
    {z : ℂ} (hz : R < ‖z‖) : schwarzHalfPlaneExtension f g z = g z := by
  by_cases hpos : 0 < z.im
  · simp [schwarzHalfPlaneExtension, hpos, hupper z hz hpos]
  · by_cases hneg : z.im < 0
    · have hzconj : R < ‖conj z‖ := by simpa using hz
      have hposconj : 0 < (conj z).im := by simpa using neg_pos.mpr hneg
      simp [schwarzHalfPlaneExtension, hpos, hneg, hupper (conj z) hzconj hposconj,
        href z hz]
    · simp [schwarzHalfPlaneExtension, hpos, hneg]

/-- The reflected function is holomorphic on the union of the two open
half-planes and any exterior domain on which the supplied analytic extension
agrees. This is an actual open domain across the exterior real rays. -/
theorem differentiableOn_schwarzHalfPlaneExtension_union_exterior
    (f g : ℂ → ℂ) {R : ℝ}
    (hf : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z)
    (hg : DifferentiableOn ℂ g {z | R < ‖z‖})
    (hupper : ∀ z : ℂ, R < ‖z‖ → 0 < z.im → f z = g z)
    (href : ∀ z : ℂ, R < ‖z‖ → g (conj z) = conj (g z)) :
    DifferentiableOn ℂ (schwarzHalfPlaneExtension f g)
      ({z | z.im ≠ 0} ∪ {z | R < ‖z‖}) := by
  have hext : DifferentiableOn ℂ (schwarzHalfPlaneExtension f g) {z | R < ‖z‖} := by
    apply hg.congr
    intro z hz
    exact schwarzHalfPlaneExtension_eq_of_conj_eq f g hupper href hz
  exact (differentiableOn_schwarzHalfPlaneExtension f g hf).union_of_isOpen hext
    (isOpen_ne_fun continuous_im continuous_const)
    (isOpen_lt continuous_const continuous_norm)

/-- A common norm bound for the upper function and the supplied axis values
also bounds its reflected extension on a symmetric parameter ball. -/
theorem norm_schwarzHalfPlaneExtension_le
    (f axis : ℂ → ℂ) {M C : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ M → 0 < z.im → ‖f z‖ ≤ C)
    (haxis : ∀ z : ℂ, ‖z‖ ≤ M → z.im = 0 → ‖axis z‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ M) : ‖schwarzHalfPlaneExtension f axis z‖ ≤ C := by
  by_cases hpos : 0 < z.im
  · simpa only [schwarzHalfPlaneExtension, if_pos hpos] using hf z hz hpos
  · by_cases hneg : z.im < 0
    · simpa [schwarzHalfPlaneExtension, hpos, hneg] using
        hf (conj z) (by simpa using hz) (by simpa using neg_pos.mpr hneg)
    · have heq : z.im = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simpa only [schwarzHalfPlaneExtension, if_neg hpos, if_neg hneg] using haxis z hz heq

end Complex
