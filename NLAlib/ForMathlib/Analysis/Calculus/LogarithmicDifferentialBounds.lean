import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic differential inequalities

Two scalar integration principles used by the entropy method. Actual
first-order inequalities yield rational bounds from the derivative at zero.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace Real

/-- Integrating the self-bounding differential inequality. The transformed
function `(1-a*t)*H(t)/t` is antitone, with limit `H'(0)` at zero. -/
theorem le_div_one_sub_mul_of_hasDerivAt_self_bound
    (H D : ℝ → ℝ) (hH : ∀ u, HasDerivAt H (D u) u)
    (hzero : H 0 = 0) {a : ℝ} (ha : 0 ≤ a)
    (hde : ∀ u, 0 < u → a * u < 1 →
      u * D u - H u ≤ a * u ^ 2 * D u)
    {s : ℝ} (hs : 0 ≤ s) (hdom : a * s < 1) :
    H s ≤ s * D 0 / (1 - a * s) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [hzero]
  let φ : ℝ → ℝ := fun u => (1 - a * u) * H u / u
  have hφ (u : ℝ) (hu : 0 < u) : HasDerivAt φ
      ((u * (1 - a * u) * D u - H u) / u ^ 2) u := by
    have h := ((((hasDerivAt_id u).const_mul a).const_sub 1).mul
      (hH u)).div (hasDerivAt_id u) hu.ne'
    exact h.congr_deriv (by simp only [id_eq, Pi.mul_apply]; ring)
  have hanti : AntitoneOn φ (Set.Ioc 0 s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 s)
    · intro u hu
      exact (hφ u hu.1).continuousAt.continuousWithinAt
    · intro u hu
      exact (hφ u (interior_subset hu).1).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Set.Ioc 0 s := interior_subset hu
      have hdomu : a * u < 1 :=
        (mul_le_mul_of_nonneg_left hu'.2 ha).trans_lt hdom
      rw [(hφ u hu'.1).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      have hd := hde u hu'.1 hdomu
      nlinarith
  have hlin : Tendsto (fun u : ℝ => 1 - a * u) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun u : ℝ => 1 - a * u) := by fun_prop
    simpa only [mul_zero, sub_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto φ (𝓝[>] 0) (𝓝 (D 0)) := by
    have h := hlin.mul ((hH 0).tendsto_slope_zero_right)
    simpa only [φ, zero_add, hzero, sub_zero, smul_eq_mul, inv_mul_eq_div,
      one_mul, mul_div_assoc] using h
  have hslope : φ s ≤ D 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hs] with u hu
    exact hanti ⟨hu.1, hu.2.le⟩ ⟨hs, le_rfl⟩ hu.2.le
  apply (le_div_iff₀ (sub_pos.mpr hdom)).mpr
  have h := mul_le_mul_of_nonneg_right hslope hs.le
  change ((1 - a * s) * H s / s) * s ≤ D 0 * s at h
  rw [div_mul_cancel₀ _ hs.ne'] at h
  nlinarith

/-- A rational Herbst integration lemma. It turns the entropy-type derivative
bound into the actual sub-gamma cumulant bound, including zero scale. -/
theorem le_affine_add_div_of_hasDerivAt_bound
    (H D : ℝ → ℝ) (hH : ∀ u, HasDerivAt H (D u) u)
    (hzero : H 0 = 0) {c C : ℝ} (hc : 0 ≤ c)
    (hde : ∀ u, 0 < u → c * u < 1 →
      u * D u - H u ≤ C * u ^ 2 / (1 - c * u) ^ 2)
    {s : ℝ} (hs : 0 ≤ s) (hdom : c * s < 1) :
    H s ≤ s * D 0 + C * s ^ 2 / (1 - c * s) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [hzero]
  let φ : ℝ → ℝ := fun u => H u / u - C * u / (1 - c * u)
  have hφ (u : ℝ) (hu : 0 < u) (hcu : c * u < 1) :
      HasDerivAt φ ((u * D u - H u) / u ^ 2 - C / (1 - c * u) ^ 2) u := by
    have h1 := (hH u).div (hasDerivAt_id u) hu.ne'
    have h2 := ((hasDerivAt_id u).const_mul C).div
      (((hasDerivAt_id u).const_mul c).const_sub 1) (sub_pos.mpr hcu).ne'
    exact (h1.sub h2).congr_deriv (by simp only [id_eq]; ring)
  have hanti : AntitoneOn φ (Set.Ioc 0 s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 s)
    · intro u hu
      exact (hφ u hu.1 ((mul_le_mul_of_nonneg_left hu.2 hc).trans_lt hdom)).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u ∈ Set.Ioc 0 s := interior_subset hu
      exact (hφ u hu'.1 ((mul_le_mul_of_nonneg_left hu'.2 hc).trans_lt hdom)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Set.Ioc 0 s := interior_subset hu
      have hcu : c * u < 1 := (mul_le_mul_of_nonneg_left hu'.2 hc).trans_lt hdom
      rw [(hφ u hu'.1 hcu).deriv]
      apply sub_nonpos.mpr
      apply (div_le_iff₀ (sq_pos_of_pos hu'.1)).mpr
      exact (hde u hu'.1 hcu).trans_eq (by ring)
  have hlim : Tendsto φ (𝓝[>] 0) (𝓝 (D 0)) := by
    have hlin : Tendsto (fun u : ℝ => C * u / (1 - c * u))
        (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun u : ℝ => C * u / (1 - c * u)) 0 := by fun_prop (disch := norm_num)
      simpa only [mul_zero, sub_zero, zero_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h := ((hH 0).tendsto_slope_zero_right).sub hlin
    simpa only [φ, zero_add, hzero, sub_zero, smul_eq_mul, inv_mul_eq_div] using h
  have hslope : φ s ≤ D 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hs] with u hu
    exact hanti ⟨hu.1, hu.2.le⟩ ⟨hs, le_rfl⟩ hu.2.le
  have h := mul_le_mul_of_nonneg_right hslope hs.le
  change (H s / s - C * s / (1 - c * s)) * s ≤ D 0 * s at h
  have he : (H s / s - C * s / (1 - c * s)) * s =
      H s - C * s ^ 2 / (1 - c * s) := by
    field_simp [hs.ne', (sub_pos.mpr hdom).ne']
  rw [he] at h
  linarith

end Real
