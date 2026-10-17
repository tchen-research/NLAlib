import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue

/-!
# Half-plane selection of exterior branches

A continuous exterior branch with a nonzero real affine slope, avoiding the real
axis above the axis, has the same imaginary sign as its slope. A vertical ray and
the intermediate value theorem prove the assertion without selecting global roots.
This supplies branch-label selection in the planar route to `trace-exponential-stahl`.
-/

noncomputable section

open Filter Metric Set
open scoped Topology

namespace Complex

private theorem norm_le_norm_add_mul_I {z : ℂ} (hz : 0 ≤ z.im) {t : ℝ} (ht : 0 ≤ t) :
    ‖z‖ ≤ ‖z + (t : ℂ) * I‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, sub_zero, mul_one, add_zero]
  nlinarith

private theorem im_pos_of_slope_pos {f : ℂ → ℂ} {R d : ℝ} {c z : ℂ}
    (hcont : ContinuousOn f {u | R < ‖u‖})
    (hreal : ∀ u, R < ‖u‖ → 0 < u.im → (f u).im ≠ 0)
    (hlim : Tendsto (fun u => f u - (d : ℂ) * u) (Bornology.cobounded ℂ) (𝓝 c))
    (hd : 0 < d) (hzR : R < ‖z‖) (hzim : 0 < z.im) : 0 < (f z).im := by
  let ray : ℝ → ℂ := fun t => z + (t : ℂ) * I
  have hnorm : ∀ t ∈ Ici (0 : ℝ), R < ‖ray t‖ := fun t ht =>
    hzR.trans_le (norm_le_norm_add_mul_I hzim.le ht)
  have him : ∀ t ∈ Ici (0 : ℝ), 0 < (ray t).im := by
    intro t ht
    simpa [ray] using add_pos_of_pos_of_nonneg hzim ht
  have hray : Continuous ray := by fun_prop
  have hg : ContinuousOn (fun t => (f (ray t)).im) (Ici (0 : ℝ)) :=
    continuous_im.continuousOn.comp
      (hcont.comp hray.continuousOn hnorm) (fun _ _ => mem_univ _)
  have ht : Tendsto (fun t : ℝ => z.im + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop z.im tendsto_id
  have hnormTop : Tendsto (fun t => ‖ray t‖) atTop atTop := by
    apply tendsto_atTop_mono _ ht
    intro t
    simpa [ray] using im_le_norm (ray t)
  have hcb : Tendsto ray atTop (Bornology.cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.mp hnormTop
  have herror : Tendsto (fun t => (f (ray t) - (d : ℂ) * ray t).im)
      atTop (𝓝 c.im) := continuous_im.tendsto c |>.comp (hlim.comp hcb)
  have hlinear : Tendsto (fun t : ℝ => d * (z.im + t)) atTop atTop :=
    ht.const_mul_atTop hd
  have hgTop : Tendsto (fun t => (f (ray t)).im) atTop atTop := by
    convert herror.add_atTop hlinear using 1
    ext t
    simp [ray]
  obtain ⟨T, hT, hgT⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hgTop.eventually_gt_atTop 0)).exists
  by_contra hnot
  have hzle : (f (ray 0)).im ≤ 0 := by simpa [ray] using le_of_not_gt hnot
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc hT
    (hg.mono (fun _ ht => ht.1)) ⟨hzle, hgT.le⟩
  exact hreal (ray t) (hnorm t ht.1) (him t ht.1) hzero

/-- A continuous exterior branch avoiding the real axis in the upper half-plane
has positive imaginary part exactly when its nonzero real affine asymptotic slope
is positive. The conclusion holds on the whole exterior upper half-plane, including
points arbitrarily close to the real axis.

atlas: trace-exponential-stahl (partial) -/
theorem im_pos_iff_slope_pos_of_tendsto_affine {f : ℂ → ℂ} {R d : ℝ} {c z : ℂ}
    (hcont : ContinuousOn f {u | R < ‖u‖})
    (hreal : ∀ u, R < ‖u‖ → 0 < u.im → (f u).im ≠ 0)
    (hlim : Tendsto (fun u => f u - (d : ℂ) * u) (Bornology.cobounded ℂ) (𝓝 c))
    (hd : d ≠ 0) (hzR : R < ‖z‖) (hzim : 0 < z.im) :
    0 < (f z).im ↔ 0 < d := by
  constructor
  · intro hf
    by_contra hdnot
    have hdneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hdnot) hd
    have hnegreal : ∀ u, R < ‖u‖ → 0 < u.im → (-f u).im ≠ 0 := by
      intro u hu him
      simpa using hreal u hu him
    have hneglim : Tendsto (fun u => -f u - ((-d : ℝ) : ℂ) * u)
        (Bornology.cobounded ℂ) (𝓝 (-c)) := by
      convert hlim.neg using 1
      ext u
      push_cast
      ring
    have hneg := im_pos_of_slope_pos hcont.neg hnegreal hneglim
      (neg_pos.mpr hdneg) hzR hzim
    simpa using (not_lt_of_ge hf.le) (neg_pos.mp hneg)
  · exact fun hdpos => im_pos_of_slope_pos hcont hreal hlim hdpos hzR hzim

end Complex
