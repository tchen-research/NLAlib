import NLAlib.ForMathlib.Analysis.Complex.CubicalCauchy
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Cauchy's formula on actual null-homologous cubical cycles

The divided difference removes the pole at the evaluation point. Its integral
vanishes by the proved topological chain-boundary theorem, leaving the actual
inverse-kernel winding factor. No scalar Cauchy formula is a hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset MeasureTheory
open scoped unitInterval
namespace Complex

/-- The actual normalized inverse-kernel integral of a finite smooth cycle.
The target-avoidance and regularity conditions are required by its theorems. -/
def cubicalWindingIntegral {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) (t : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * cubicalCurveIntegral (fun z => (z - t)⁻¹) Γ

private theorem curveIntegral_div_sub_eq_add_dslope
    {a b t : ℂ} (γ : Path a b) {f : ℂ → ℂ}
    (hoff : ∀ r, γ r ≠ t)
    (h1 : CurveIntegrable (fun z => (f z / (z - t)) • ContinuousLinearMap.id ℂ ℂ) γ)
    (h2 : CurveIntegrable (fun z => (f t / (z - t)) • ContinuousLinearMap.id ℂ ℂ) γ) :
    curveIntegral (fun z => (f z / (z - t)) • ContinuousLinearMap.id ℂ ℂ) γ =
      curveIntegral (fun z => dslope f t z • ContinuousLinearMap.id ℂ ℂ) γ +
        f t * curveIntegral (fun z => (z - t)⁻¹ • ContinuousLinearMap.id ℂ ℂ) γ := by
  have he : curveIntegral (fun z => dslope f t z • ContinuousLinearMap.id ℂ ℂ) γ =
      curveIntegral (fun z => (f z / (z - t)) • ContinuousLinearMap.id ℂ ℂ -
        (f t / (z - t)) • ContinuousLinearMap.id ℂ ℂ) γ := by
    rw [curveIntegral_def, curveIntegral_def]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using hr
    simp only [curveIntegralFun_def, γ.extend_apply hr', dslope_of_ne f (hoff ⟨r, hr'⟩),
      slope_def_field, sub_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  rw [curveIntegral_fun_sub h1 h2] at he
  have hω : (fun z => (f t / (z - t)) • ContinuousLinearMap.id ℂ ℂ) =
      fun z => f t • ((z - t)⁻¹ • ContinuousLinearMap.id ℂ ℂ) := by
    funext z
    simp only [div_eq_mul_inv, mul_smul]
  rw [hω, curveIntegral_fun_smul] at he
  change _ = _ - f t * _ at he
  linear_combination -he

/-- The raw Cauchy factorization for an actual finite null-homologous C1
cycle in an arbitrary open planar domain. A continuous singular cubical
filling supplies null homology, and the actual Cauchy equality is proved. -/
theorem cubicalCurveIntegral_div_sub_eq_mul_inv_sub_of_isNullHomologous
    {Ω : Set ℂ} {f : ℂ → ℂ} {t : ℂ}
    (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) (ht : t ∈ Ω)
    (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hoff : ∀ γ ∈ Γ.support, ∀ r, (γ r : ℂ) ≠ t)
    (hnull : Cubical.IsNullHomologous Γ) :
    cubicalCurveIntegral (fun z => f z / (z - t)) Γ =
      f t * cubicalCurveIntegral (fun z => (z - t)⁻¹) Γ := by
  have hds : DifferentiableOn ℂ (dslope f t) Ω :=
    (differentiableOn_dslope (hΩ.mem_nhds ht)).mpr hf
  have hz := cubicalCurveIntegral_eq_zero_of_isNullHomologous hΩ hds Γ hΓ hnull
  have he : cubicalCurveIntegral (fun z => f z / (z - t)) Γ =
      cubicalCurveIntegral (dslope f t) Γ +
        f t * cubicalCurveIntegral (fun z => (z - t)⁻¹) Γ := by
    unfold cubicalCurveIntegral
    simp only [Finsupp.linearCombination_apply, Finsupp.sum]
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro γ hγ
    have hne (z : ℂ) (hz : z ∈ Ω \ {t}) : z - t ≠ 0 := sub_ne_zero.mpr hz.2
    have hmem (r : I) : cubicalPath γ r ∈ Ω \ {t} := ⟨(γ r).property, hoff γ hγ r⟩
    have h1 : CurveIntegrable
        (fun z => (f z / (z - t)) • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) :=
      ((hf.continuousOn.mono sdiff_subset).div (continuousOn_id.sub continuousOn_const) hne).smul
        continuousOn_const |>.curveIntegrable_of_contDiffOn (hΓ γ hγ) hmem
    have h2 : CurveIntegrable
        (fun z => (f t / (z - t)) • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) :=
      (continuousOn_const.div (continuousOn_id.sub continuousOn_const) hne).smul
        continuousOn_const |>.curveIntegrable_of_contDiffOn (hΓ γ hγ) hmem
    rw [curveIntegral_div_sub_eq_add_dslope (cubicalPath γ) (hoff γ hγ) h1 h2]
    simp only [zsmul_eq_mul]
    ring
  rwa [hz, zero_add] at he

/-- A finite null-homologous C1 cycle with actual winding one satisfies the
usual scalar Cauchy formula, including in multiply connected domains. Every
analytic cancellation is derived from the continuous cubical filling.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem two_pi_i_inv_mul_cubicalCurveIntegral_div_sub_eq_of_isNullHomologous
    {Ω : Set ℂ} {f : ℂ → ℂ} {t : ℂ}
    (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) (ht : t ∈ Ω)
    (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hoff : ∀ γ ∈ Γ.support, ∀ r, (γ r : ℂ) ≠ t)
    (hnull : Cubical.IsNullHomologous Γ) (hw : cubicalWindingIntegral Γ t = 1) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ * cubicalCurveIntegral (fun z => f z / (z - t)) Γ = f t := by
  rw [cubicalCurveIntegral_div_sub_eq_mul_inv_sub_of_isNullHomologous hΩ hf ht Γ hΓ hoff hnull]
  calc
    _ = f t * cubicalWindingIntegral Γ t := by unfold cubicalWindingIntegral; ring
    _ = f t := by rw [hw, mul_one]

end Complex
