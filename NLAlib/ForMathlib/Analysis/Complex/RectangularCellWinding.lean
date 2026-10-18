import NLAlib.ForMathlib.Analysis.Calculus.Path
import NLAlib.ForMathlib.Analysis.Complex.CurveLogPrimitive

/-! # The actual inverse-kernel integral on a rectangular cell

Principal-log primitives evaluate the four native straight edges.
The branch change at the left edge gives the actual period `2*pi*i`
for every strictly interior target. No Cauchy or winding-one premise
is supplied; corners and stationary derivatives remain admissible.
Atlas: `gauss-remainder-contour-kernel`, grid prerequisite only.
-/

noncomputable section
open Set MeasureTheory
open scoped unitInterval
namespace Complex

/-- A rotated log primitive evaluates a native straight edge whenever
the actual rotated edge avoids the principal cut. -/
theorem curveIntegral_inv_sub_segment_eq_log_mul_sub_of_slitPlane
    {a b τ r : ℂ} (hr : r ≠ 0)
    (hs : ∀ t, r * (Path.segment a b t - τ) ∈ slitPlane) :
    curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ) (Path.segment a b) =
      log (r * (b - τ)) - log (r * (a - τ)) := by
  let U : Set ℂ := range (Path.segment a b)
  have hslit (z : ℂ) (hz : z ∈ U) : r * (z - τ) ∈ slitPlane := by
    obtain ⟨t, rfl⟩ := hz
    exact hs t
  have hne (z : ℂ) (hz : z ∈ U) : z - τ ≠ 0 :=
    fun he => slitPlane_ne_zero (hslit z hz) (by rw [he, mul_zero])
  have hG (z : ℂ) (hz : z ∈ U) :
      HasDerivAt (fun z => log (r * (z - τ))) (z - τ)⁻¹ z := by
    have hd := (((hasDerivAt_id z).sub_const τ).const_mul r).clog (hslit z hz)
    simp only [id_eq, mul_one] at hd
    apply hd.congr_deriv
    field_simp [hr, hne z hz]
  have hg : ContinuousOn (fun z : ℂ => (z - τ)⁻¹) U :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  exact curveIntegral_eq_sub_of_hasDerivAt (Path.segment a b) hG hg
    (Path.contDiffOn_extend_segment a b 1) (fun t => mem_range_self t)

private theorem log_neg_eq_sub_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    log (-z) = log z - (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_sub_pi_of_im_pos hz]

private theorem log_neg_eq_add_of_im_neg {z : ℂ} (hz : z.im < 0) :
    log (-z) = log z + (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_add_pi_of_im_neg hz]

private theorem im_segment_horizontal (x y h : ℝ) (t : I) :
    (Path.segment ((x : ℂ) + h * Complex.I) ((y : ℂ) + h * Complex.I) t).im = h := by
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module, add_im, smul_im,
    ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, zero_mul, add_zero, zero_add]
  ring

private theorem re_segment_vertical (x c d : ℝ) (t : I) :
    (Path.segment ((x : ℂ) + c * Complex.I) ((x : ℂ) + d * Complex.I) t).re = x := by
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module, add_re, smul_re,
    ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

/-- The actual counterclockwise sum of four increasing-coordinate native
edges has inverse-kernel integral exactly `2*pi*i` at every interior point.
Source: elementary principal-log rectangle calculation, the cell-index
step of the general-contour Gauss route.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem curveIntegral_inv_sub_rectangle_eq_two_pi_I
    {a b c d : ℝ} {τ : ℂ}
    (ha : a < τ.re) (hb : τ.re < b) (hc : c < τ.im) (hd : τ.im < d) :
    curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        (Path.segment ((a : ℂ) + c * Complex.I) ((b : ℂ) + c * Complex.I)) +
      curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        (Path.segment ((b : ℂ) + c * Complex.I) ((b : ℂ) + d * Complex.I)) -
      curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        (Path.segment ((a : ℂ) + d * Complex.I) ((b : ℂ) + d * Complex.I)) -
      curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        (Path.segment ((a : ℂ) + c * Complex.I) ((a : ℂ) + d * Complex.I)) =
      (2 * Real.pi * Complex.I : ℂ) := by
  have hbottom := curveIntegral_inv_sub_segment_eq_log_mul_sub_of_slitPlane
    (τ := τ) (r := (1 : ℂ)) one_ne_zero (a := (a : ℂ) + c * Complex.I) (b := (b : ℂ) + c * Complex.I) (by
      intro t
      rw [one_mul]
      apply mem_slitPlane_iff.mpr
      right
      have h : (Path.segment ((a : ℂ) + c * Complex.I) ((b : ℂ) + c * Complex.I) t - τ).im < 0 := by
        rw [sub_im, im_segment_horizontal]
        linarith
      exact ne_of_lt h)
  have hright := curveIntegral_inv_sub_segment_eq_log_mul_sub_of_slitPlane
    (τ := τ) (r := (1 : ℂ)) one_ne_zero (a := (b : ℂ) + c * Complex.I) (b := (b : ℂ) + d * Complex.I) (by
      intro t
      rw [one_mul]
      apply mem_slitPlane_iff.mpr
      left
      rw [sub_re, re_segment_vertical]
      linarith)
  have htop := curveIntegral_inv_sub_segment_eq_log_mul_sub_of_slitPlane
    (τ := τ) (r := (1 : ℂ)) one_ne_zero (a := (a : ℂ) + d * Complex.I) (b := (b : ℂ) + d * Complex.I) (by
      intro t
      rw [one_mul]
      apply mem_slitPlane_iff.mpr
      right
      have h : 0 < (Path.segment ((a : ℂ) + d * Complex.I) ((b : ℂ) + d * Complex.I) t - τ).im := by
        rw [sub_im, im_segment_horizontal]
        linarith
      exact ne_of_gt h)
  have hleft := curveIntegral_inv_sub_segment_eq_log_mul_sub_of_slitPlane
    (τ := τ) (r := (-1 : ℂ)) (by norm_num) (a := (a : ℂ) + c * Complex.I) (b := (a : ℂ) + d * Complex.I) (by
      intro t
      apply mem_slitPlane_iff.mpr
      left
      rw [neg_one_mul, neg_re, sub_re, re_segment_vertical]
      linarith)
  simp only [one_mul, neg_one_mul] at hbottom hright htop hleft
  rw [hbottom, hright, htop, hleft]
  have hpos : 0 < (((a : ℂ) + d * Complex.I) - τ).im := by simp; linarith
  have hneg : (((a : ℂ) + c * Complex.I) - τ).im < 0 := by simp; linarith
  rw [log_neg_eq_sub_of_im_pos hpos, log_neg_eq_add_of_im_neg hneg]
  ring

private theorem re_rotated_segment_pos {a b τ r : ℂ}
    (ha : 0 < (r * (a - τ)).re) (hb : 0 < (r * (b - τ)).re) (t : I) :
    0 < (r * (Path.segment a b t - τ)).re := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  have he : (r * (Path.segment a b t - τ)).re =
      (1 - (t : ℝ)) * (r * (a - τ)).re + (t : ℝ) * (r * (b - τ)).re := by
    simp [Path.segment_apply, AffineMap.lineMap_apply_module, mul_re, sub_re, sub_im,
      add_re, add_im]
    ring
  rw [he]
  by_cases ht : (t : ℝ) = 1
  · simpa [ht] using hb
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) ha) (mul_nonneg ht0 hb.le)

/-- Four actual straight edges telescope to zero when their vertices share
a rotated principal-log half-plane relative to the target. -/
theorem curveIntegral_inv_sub_quadrilateral_eq_zero_of_re_pos
    {v₀ v₁ v₂ v₃ τ r : ℂ} (hr : r ≠ 0)
    (h₀ : 0 < (r * (v₀ - τ)).re) (h₁ : 0 < (r * (v₁ - τ)).re)
    (h₂ : 0 < (r * (v₂ - τ)).re) (h₃ : 0 < (r * (v₃ - τ)).re) :
    curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ) (Path.segment v₀ v₁) +
      curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ) (Path.segment v₁ v₂) -
      curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ) (Path.segment v₃ v₂) -
      curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ) (Path.segment v₀ v₃) = 0 := by
  have hs {a b : ℂ} (ha : 0 < (r * (a - τ)).re) (hb : 0 < (r * (b - τ)).re) (t : I) :
      r * (Path.segment a b t - τ) ∈ slitPlane :=
    mem_slitPlane_iff.mpr (Or.inl (re_rotated_segment_pos ha hb t))
  rw [curveIntegral_inv_sub_segment_eq_log_mul_sub_of_slitPlane hr (hs h₀ h₁),
    curveIntegral_inv_sub_segment_eq_log_mul_sub_of_slitPlane hr (hs h₁ h₂),
    curveIntegral_inv_sub_segment_eq_log_mul_sub_of_slitPlane hr (hs h₃ h₂),
    curveIntegral_inv_sub_segment_eq_log_mul_sub_of_slitPlane hr (hs h₀ h₃)]
  ring

/-- The actual four-edge inverse integral vanishes at every target strictly
outside the closed coordinate rectangle. Together with the interior period,
this isolates individual cell coefficients in a finite grid. -/
theorem curveIntegral_inv_sub_rectangle_eq_zero_of_outside
    {a b c d : ℝ} {τ : ℂ} (hab : a ≤ b) (hcd : c ≤ d)
    (hout : τ.re < a ∨ b < τ.re ∨ τ.im < c ∨ d < τ.im) :
    curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        (Path.segment ((a : ℂ) + c * Complex.I) ((b : ℂ) + c * Complex.I)) +
      curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        (Path.segment ((b : ℂ) + c * Complex.I) ((b : ℂ) + d * Complex.I)) -
      curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        (Path.segment ((a : ℂ) + d * Complex.I) ((b : ℂ) + d * Complex.I)) -
      curveIntegral (fun z => (z - τ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        (Path.segment ((a : ℂ) + c * Complex.I) ((a : ℂ) + d * Complex.I)) = 0 := by
  rcases hout with h | h | h | h
  · apply curveIntegral_inv_sub_quadrilateral_eq_zero_of_re_pos (r := 1) one_ne_zero
    all_goals simp; linarith
  · apply curveIntegral_inv_sub_quadrilateral_eq_zero_of_re_pos (r := -1) (by norm_num)
    all_goals simp; linarith
  · apply curveIntegral_inv_sub_quadrilateral_eq_zero_of_re_pos (r := -Complex.I) (by simp)
    all_goals simp [mul_re, mul_im]; linarith
  · apply curveIntegral_inv_sub_quadrilateral_eq_zero_of_re_pos (r := Complex.I) I_ne_zero
    all_goals simp [mul_re, mul_im]; linarith

end Complex
