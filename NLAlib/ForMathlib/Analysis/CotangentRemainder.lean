import NLAlib.ForMathlib.Analysis.CotangentIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Concavity of the regularized cotangent

Elementary polynomial sine and cosine bounds prove the second-derivative sign.
The removable value at zero is the totalized cotangent-minus-reciprocal value.
-/
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
namespace NLAlib

/-- The quartic Taylor polynomial bounds cosine above on the positive real axis.
Source: direct differentiation and the cubic sine lower bound. -/
theorem cos_le_one_sub_sq_add_quartic {x : ℝ} (hx : 0 ≤ x) :
    cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f := fun x : ℝ => 1 - x ^ 2 / 2 + x ^ 4 / 24 - cos x
  have hd (x : ℝ) : HasDerivAt f (sin x - x + x ^ 3 / 6) x := by
    have h := (((hasDerivAt_const x 1).sub (((hasDerivAt_id x).pow 2).div_const 2)).add
      (((hasDerivAt_id x).pow 4).div_const 24)).sub (Real.hasDerivAt_cos x)
    exact h.congr_deriv (by dsimp only [id_eq]; ring)
  have hm : MonotoneOn f (Ici (0 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x hx => (hd x).continuousAt.continuousWithinAt)
      (fun x hx => (hd x).hasDerivWithinAt)
      (fun x hx => by have h := sin_ge_sub_cube (show 0 ≤ x from (interior_subset hx)); linarith)
  have h := hm (by simp) hx hx
  dsimp [f] at h
  norm_num at h
  linarith

/-- On the positive half quadrant, `sin³x≥x³ cos x`.
Source: focused reroutes, the regularized-cotangent concavity calculation.
Cubic sine and quartic cosine bounds replace the logarithmic differentiation argument. -/
theorem mul_cos_le_sin_cube {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ π / 2) :
    x ^ 3 * cos x ≤ sin x ^ 3 := by
  have hx2 : x ≤ 2 := by linarith [pi_lt_four]
  have hxSq : x ^ 2 ≤ 4 := by nlinarith
  have ha : 0 ≤ x - x ^ 3 / 6 := by
    have h := mul_nonneg hx (show 0 ≤ 1 - x ^ 2 / 6 by nlinarith)
    nlinarith
  have hsin := pow_le_pow_left₀ ha (sin_ge_sub_cube hx) 3
  have hcos := mul_le_mul_of_nonneg_left (cos_le_one_sub_sq_add_quartic hx) (pow_nonneg hx 3)
  have heq : (x - x ^ 3 / 6) ^ 3 - x ^ 3 * (1 - x ^ 2 / 2 + x ^ 4 / 24) =
      x ^ 7 * (9 - x ^ 2) / 216 := by ring
  have hnon : 0 ≤ x ^ 7 * (9 - x ^ 2) / 216 :=
    div_nonneg (mul_nonneg (pow_nonneg hx _) (by linarith)) (by norm_num)
  rw [← heq] at hnon
  linarith

/-- The regularized cotangent has a linear absolute bound near its removable zero.
Source: the cubic-scale numerator bound and Jordan's sine lower bound. -/
theorem abs_cot_sub_one_div_le {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ π / 2) :
    |Real.cot x - 1 / x| ≤ π * x / 4 := by
  by_cases hx0 : x = 0
  · subst x
    simp [Real.cot_eq_cos_div_sin]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hxpos (by linarith [pi_pos])
  have hup : Real.cot x - 1 / x ≤ 0 := sub_nonpos.mpr (cot_le_one_div hxpos hxπ)
  have hlow : -(π * x / 4) ≤ Real.cot x - 1 / x := by
    rw [Real.cot_eq_cos_div_sin]
    have heq : cos x / sin x - 1 / x = (x * cos x - sin x) / (x * sin x) := by field_simp
    rw [heq, le_div_iff₀ (mul_pos hxpos hs)]
    have hc := mul_le_mul_of_nonneg_left (one_sub_sq_div_two_le_cos (x := x)) hx
    have hl := mul_le_mul_of_nonneg_left (mul_le_sin hx hxπ) (show 0 ≤ π * x ^ 2 / 4 by positivity)
    have hl' : x ^ 3 / 2 ≤ π * x ^ 2 / 4 * sin x := by
      have heq : π * x ^ 2 / 4 * (2 / π * x) = x ^ 3 / 2 := by field_simp; ring
      rw [heq] at hl
      exact hl
    have hsin := Real.sin_le hx
    nlinarith
  rw [abs_of_nonpos hup]
  linarith

/-- Cotangent minus the reciprocal is continuous on the closed positive half quadrant.
Source: the removable zero bound and the ordinary quotient rule away from zero. -/
theorem continuousOn_cot_sub_one_div :
    ContinuousOn (fun x : ℝ => Real.cot x - 1 / x) (Icc 0 (π / 2)) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    have hlim : Tendsto (fun x : ℝ => π * x / 4) (𝓝[Icc 0 (π / 2)] 0) (𝓝 0) := by
      have hc : Continuous (fun x : ℝ => π * x / 4) := (continuous_const.mul continuous_id).div_const 4
      simpa only [mul_zero, zero_div] using
        (hc.continuousAt (x := (0 : ℝ))).continuousWithinAt (s := Icc 0 (π / 2)) |>.tendsto
    have hab : ∀ᶠ x : ℝ in 𝓝[Icc 0 (π / 2)] 0, |Real.cot x - 1 / x| ≤ π * x / 4 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact abs_cot_sub_one_div_le hx.1 hx.2
    have h := squeeze_zero' (Eventually.of_forall (fun x : ℝ => abs_nonneg (Real.cot x - 1 / x))) hab hlim
    have ht : Tendsto (fun x : ℝ => Real.cot x - 1 / x) (𝓝[Icc 0 (π / 2)] 0) (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [Real.norm_eq_abs] using h
    change Tendsto (fun x : ℝ => Real.cot x - 1 / x) (𝓝[Icc 0 (π / 2)] 0) (𝓝 (Real.cot 0 - 1 / 0))
    simpa only [Real.cot_eq_cos_div_sin, cos_zero, sin_zero, div_zero, sub_self] using ht
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hs : sin x ≠ 0 := (sin_pos_of_pos_of_lt_pi hxpos (by linarith [hx.2, pi_pos])).ne'
    exact ((hasDerivAt_cot hs).continuousAt.sub (continuousAt_const.div continuousAt_id hx0)).continuousWithinAt

/-- Cotangent minus the reciprocal is concave, including its removable value zero.
Source: focused reroutes, the sharp logarithmic lower-constant midpoint argument. -/
theorem concaveOn_cot_sub_one_div :
    ConcaveOn ℝ (Icc 0 (π / 2)) (fun x : ℝ => Real.cot x - 1 / x) := by
  let f' := fun x : ℝ => -1 / sin x ^ 2 + 1 / x ^ 2
  let f'' := fun x : ℝ => 2 * cos x / sin x ^ 3 - 2 / x ^ 3
  have hargs (x : ℝ) (hx : x ∈ interior (Icc (0 : ℝ) (π / 2))) :
      0 < x ∧ x < π / 2 ∧ 0 < sin x := by
    rw [interior_Icc] at hx
    exact ⟨hx.1, hx.2, sin_pos_of_pos_of_lt_pi hx.1 (by linarith [pi_pos, hx.2])⟩
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (π / 2))
    continuousOn_cot_sub_one_div (f' := f') (f'' := f'')
  · intro x hx
    obtain ⟨hx0, hxπ, hs⟩ := hargs x hx
    have h := (hasDerivAt_cot hs.ne').sub ((hasDerivAt_const x 1).div (hasDerivAt_id x) hx0.ne')
    have hd : HasDerivAt (fun x : ℝ => Real.cot x - 1 / x) (f' x) x :=
      h.congr_deriv (by dsimp [f']; ring)
    exact hd.hasDerivWithinAt
  · intro x hx
    obtain ⟨hx0, hxπ, hs⟩ := hargs x hx
    have h := ((hasDerivAt_const x (-1 : ℝ)).div ((Real.hasDerivAt_sin x).pow 2) (pow_ne_zero 2 hs.ne')).add
      ((hasDerivAt_const x 1).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0.ne'))
    have hd : HasDerivAt f' (f'' x) x := by
      apply h.congr_deriv
      dsimp [f'']
      field_simp
      ring
    exact hd.hasDerivWithinAt
  · intro x hx
    obtain ⟨hx0, hxπ, hs⟩ := hargs x hx
    dsimp [f'']
    rw [sub_nonpos, div_le_div_iff₀ (pow_pos hs 3) (pow_pos hx0 3)]
    have h := mul_cos_le_sin_cube hx0.le hxπ.le
    nlinarith

/-- The midpoint value of the regularized cotangent bounds its integral above.
Source: focused reroutes, midpoint concavity in the sharp lower-constant proof. -/
theorem integral_cot_sub_one_div_le_mul_midpoint {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ π / 2) :
    (∫ x in a..b, Real.cot x - 1 / x) ≤
      (b - a) * (Real.cot ((a + b) / 2) - 1 / ((a + b) / 2)) := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) (π / 2) := Icc_subset_Icc ha hb
  have hc := (concaveOn_cot_sub_one_div.subset hsub (convex_Icc a b)).neg
  have h := mul_midpoint_le_integral_of_convexOn hab
    (continuousOn_cot_sub_one_div.mono hsub).neg hc
  simp only [Pi.neg_apply] at h
  rw [intervalIntegral.integral_neg] at h
  linarith

end NLAlib
