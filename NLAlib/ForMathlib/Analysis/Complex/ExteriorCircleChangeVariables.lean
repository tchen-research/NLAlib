import NLAlib.ForMathlib.Analysis.Complex.FreeLoopHomotopy
import NLAlib.ForMathlib.Analysis.Complex.ExteriorCircleCauchy
import NLAlib.ForMathlib.Analysis.Complex.CircleIntegrationByParts
import NLAlib.ForMathlib.MeasureTheory.CirclePath

/-!
# Changing exterior-circle coordinates

A holomorphic map close to a nonzero real dilation of a large circle takes
that circle to a freely homotopic exterior loop. The derivative pullback has
the same integral as an ordinary circle in that exterior domain. This is the
common-contour replacement required by the planar inverse-branch proof of
`trace-exponential-stahl`; the contour equality is proved from the geometric
bound, rather than assumed.
-/

noncomputable section

open Set Metric Complex Filter
open scoped Topology unitInterval

namespace Complex

/-- A circle image sufficiently close to a real dilation can be replaced by
the dilated circle in an exterior holomorphy domain. Negative dilation still
preserves counterclockwise orientation. The strict closeness estimate keeps
the entire straight free homotopy outside the forbidden disk. -/
theorem circleIntegral_comp_mul_deriv_eq_of_close_to_real_mul
    {f g : ℂ → ℂ} {R S r a : ℝ}
    (hr : 0 < r)
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (hg : DifferentiableOn ℂ g {z | S < ‖z‖}) (hSr : S < r)
    (hclose : ∀ u ∈ sphere (0 : ℂ) r, ‖g u - (a : ℂ) * u‖ < |a| * r - R) :
    (∮ u in C(0, r), f (g u) * deriv g u) =
      ∮ z in C(0, |a| * r), f z := by
  have hU : IsOpen {z : ℂ | S < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hV : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hc : sphere (0 : ℂ) |r| ⊆ {z : ℂ | S < ‖z‖} := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa [mem_sphere_iff_norm, abs_of_pos hr] using hz
    simpa [hz'] using hSr
  have hgc : ContinuousOn g (range (circlePath 0 r)) :=
    hg.continuousOn.mono (by
      rintro z ⟨t, rfl⟩
      apply hc
      exact circleMap_mem_sphere' 0 r _)
  let γ₀ := (circlePath 0 r).map' hgc
  let γ₁ := circlePath 0 (a * r)
  let z : ℝ → ℂ := fun t => circleMap 0 r (2 * Real.pi * t)
  let ψ : ℝ × ℝ → ℂ := fun t =>
    ((1 - t.1 : ℝ) : ℂ) * (g (z t.2) - (a : ℂ) * z t.2) + (a : ℂ) * z t.2
  have hgz : Continuous (fun t => g (z t)) := by
    exact hg.continuousOn.comp_continuous
      ((continuous_circleMap 0 r).comp (continuous_const.mul continuous_id))
      (fun t => hc (circleMap_mem_sphere' 0 r _))
  have hz : Continuous z :=
    (continuous_circleMap 0 r).comp (continuous_const.mul continuous_id)
  have hψ : Continuous ψ := by
    exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).mul
      ((hgz.comp continuous_snd).sub (continuous_const.mul (hz.comp continuous_snd)))).add
      (continuous_const.mul (hz.comp continuous_snd))
  have hψV : ∀ t ∈ Icc (0 : ℝ × ℝ) 1, ψ t ∈ {z : ℂ | R < ‖z‖} := by
    intro t ht
    have hnormz : ‖z t.2‖ = r := by simp [z, abs_of_pos hr]
    have hnorma : ‖(a : ℂ) * z t.2‖ = |a| * r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormz]
    have herr := hclose (z t.2) (by simpa [mem_sphere_iff_norm] using hnormz)
    have htlo : 0 ≤ t.1 := ht.1.1
    have hthi : t.1 ≤ 1 := ht.2.1
    have hcoeff : ‖((1 - t.1 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hsmall : ‖((1 - t.1 : ℝ) : ℂ) *
        (g (z t.2) - (a : ℂ) * z t.2)‖ ≤ ‖g (z t.2) - (a : ℂ) * z t.2‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hcoeff
    have htriangle : ‖(a : ℂ) * z t.2‖ ≤ ‖ψ t‖ +
        ‖((1 - t.1 : ℝ) : ℂ) * (g (z t.2) - (a : ℂ) * z t.2)‖ := by
      have h := norm_sub_le (ψ t)
        (((1 - t.1 : ℝ) : ℂ) * (g (z t.2) - (a : ℂ) * z t.2))
      simpa only [ψ, add_sub_cancel_left] using h
    change R < ‖ψ t‖
    linarith
  have hleft : ∀ t ∈ Icc (0 : ℝ) 1, γ₀.extend t = ψ (0, t) := by
    intro t ht
    rw [Path.extend_apply _ ht]
    change g (z t) = ψ (0, t)
    simp [ψ]
  have hright : ∀ t ∈ Icc (0 : ℝ) 1, γ₁.extend t = ψ (1, t) := by
    intro t ht
    rw [circlePath_extend_apply ht]
    simp [ψ, z, circleMap, Complex.ofReal_mul, mul_assoc]
  have hloop : ∀ t ∈ Icc (0 : ℝ) 1, ψ (t, 0) = ψ (t, 1) := by
    intro t _
    simp [ψ, z, circleMap]
  have heq := curveIntegral_eq_of_differentiableOn_of_freeHomotopy γ₀ γ₁ hψ
    hV hf hψV hleft hright hloop
    (contDiffOn_circlePath_map_extend hU hg hc hgc)
    (contDiffOn_circlePath_extend 0 (a * r))
  rw [curveIntegral_circlePath_map_eq_circleIntegral_mul_deriv f hU hg hc hgc,
    curveIntegral_circlePath_eq_circleIntegral] at heq
  rw [heq]
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
  · rw [abs_of_neg (lt_of_not_ge ha), neg_mul]
    exact (circleIntegral.integral_neg_radius_eq f 0 (a * r)).symm

/-- An affine asymptote with nonzero real slope suffices to replace every
sufficiently large image circle by any fixed circle in an exterior
holomorphy domain. This derives the geometric homotopy bound from the limit
at infinity. -/
theorem eventually_circleIntegral_comp_mul_deriv_eq_of_tendsto_affine
    {f g : ℂ → ℂ} {R S ρ a : ℝ} {q : ℂ}
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (hg : DifferentiableOn ℂ g {z | S < ‖z‖}) (ha : a ≠ 0)
    (hlim : Tendsto (fun u => g u - (a : ℂ) * u)
      (Bornology.cobounded ℂ) (𝓝 q)) (hρ : 0 < ρ) (hRρ : R < ρ) :
    ∀ᶠ r : ℝ in atTop,
      (∮ u in C(0, r), f (g u) * deriv g u) = ∮ z in C(0, ρ), f z := by
  have habs : 0 < |a| := abs_pos.mpr ha
  have hbound : ∀ᶠ u in Bornology.cobounded ℂ,
      ‖g u - (a : ℂ) * u‖ < ‖q‖ + 1 :=
    hlim.norm.eventually_lt_const (lt_add_one _)
  obtain ⟨T, _, hT⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hbound
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop S,
    eventually_ge_atTop T, eventually_gt_atTop ((R + ‖q‖ + 1) / |a|)]
    with r hr hSr hTr hlarge
  have hmul : R + ‖q‖ + 1 < r * |a| := (div_lt_iff₀ habs).mp hlarge
  have hclose : ∀ u ∈ sphere (0 : ℂ) r,
      ‖g u - (a : ℂ) * u‖ < |a| * r - R := by
    intro u hu
    have hnorm : ‖u‖ = r := by simpa [mem_sphere_iff_norm] using hu
    have hsmall := hT (x := u) (by change T ≤ ‖u‖; simpa only [hnorm] using hTr)
    nlinarith
  have hRr : R < |a| * r := by nlinarith [norm_nonneg q]
  exact (circleIntegral_comp_mul_deriv_eq_of_close_to_real_mul hr hf hg hSr hclose).trans
    (NLAlib.circleIntegral_eq_of_differentiableOn_exterior hf (mul_pos habs hr) hρ hRr hRρ)

/-- An exterior holomorphic inverse coordinate changes the exponential
circle moment into the negative exponential moment of the inverse. Both
the common-contour replacement and integration by parts are proved; the
only inverse premise is the pointwise identity near infinity. -/
theorem eventually_circleIntegral_exp_eq_neg_circleIntegral_exp_mul_of_inverse
    {F g : ℂ → ℂ} {R S ρ a : ℝ} {q : ℂ}
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (hg : DifferentiableOn ℂ g {z | S < ‖z‖}) (ha : a ≠ 0)
    (hlim : Tendsto (fun u => g u - (a : ℂ) * u)
      (Bornology.cobounded ℂ) (𝓝 q))
    (hinverse : ∀ᶠ u in Bornology.cobounded ℂ, F (g u) = u)
    (hρ : 0 < ρ) (hRρ : R < ρ) :
    ∀ᶠ r : ℝ in atTop,
      (∮ z in C(0, ρ), exp (F z)) = -(∮ u in C(0, r), exp u * g u) := by
  have hmoment := eventually_circleIntegral_comp_mul_deriv_eq_of_tendsto_affine
    (Complex.differentiable_exp.comp_differentiableOn hF) hg ha hlim hρ hRρ
  obtain ⟨T, _, hT⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hinverse
  filter_upwards [hmoment, eventually_gt_atTop (0 : ℝ), eventually_gt_atTop S,
    eventually_ge_atTop T] with r hmoment hr hSr hTr
  simp only [Function.comp_def] at hmoment
  have hpoint : EqOn (fun u => exp (F (g u)) * deriv g u)
      (fun u => exp u * deriv g u) (sphere (0 : ℂ) r) := by
    intro u hu
    have hnorm : ‖u‖ = r := by simpa [mem_sphere_iff_norm] using hu
    change exp (F (g u)) * deriv g u = exp u * deriv g u
    rw [hT (x := u) (by change T ≤ ‖u‖; simpa only [hnorm] using hTr)]
  rw [circleIntegral.integral_congr hr.le hpoint] at hmoment
  have hU : IsOpen {z : ℂ | S < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hc : sphere (0 : ℂ) r ⊆ {z : ℂ | S < ‖z‖} := by
    intro u hu
    have hnorm : ‖u‖ = r := by simpa [mem_sphere_iff_norm] using hu
    change S < ‖u‖
    simpa only [hnorm] using hSr
  rw [circleIntegral.integral_exp_mul_deriv_eq_neg_integral_exp_mul hr.le hU hc hg]
    at hmoment
  exact hmoment.symm

end Complex
