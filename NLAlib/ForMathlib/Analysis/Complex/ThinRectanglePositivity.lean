import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Positivity from thin rectangular contours

The counterclockwise boundary integral is written as four ordinary interval
integrals. Schwarz reflection pairs the horizontal edges, and the elementary
inequality `Im (exp (i ε) z) ≥ -|sin ε| |z|` bounds the possible negative part.
Together with uniformly bounded vertical edges, this gives an explicit error
of order `ε` and positivity for a fixed contour moment.

These are scalar helpers for the planar root-sum approach to atlas
`trace-exponential-stahl`. Identifying the matrix density with these contour
moments is a separate analytic bridge.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open scoped Interval ComplexConjugate

namespace Complex

/-- The counterclockwise integral around the rectangle with real interval
`[a,b]` and imaginary interval `[c,d]`, parametrized along its four edges.
The definition is total; actual edge integrability is supplied by applications. -/
def rectangleBoundaryIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f (x + c * I)) - (∫ x in a..b, f (x + d * I)) +
    I * (∫ y in c..d, f (b + y * I)) - I * (∫ y in c..d, f (a + y * I))

/-- Rotating a complex number with nonnegative imaginary part through an
angle whose cosine is nonnegative gives an imaginary part bounded below by
`-|sin θ|` times its norm. -/
theorem neg_abs_sin_mul_norm_le_im_exp_mul {θ : ℝ} {z : ℂ}
    (hcos : 0 ≤ Real.cos θ) (hz : 0 ≤ z.im) :
    -(|Real.sin θ| * ‖z‖) ≤ (exp (θ * I) * z).im := by
  have hre := abs_re_le_norm z
  have hs : -(Real.sin θ * z.re) ≤ |Real.sin θ| * ‖z‖ :=
    (neg_le_abs _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hre (abs_nonneg _))
  have hc := mul_nonneg hcos hz
  simpa only [mul_im, exp_re, exp_im, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_zero, zero_mul, add_zero, Real.exp_zero, one_mul]
    using (show -(|Real.sin θ| * ‖z‖) ≤ Real.cos θ * z.im + Real.sin θ * z.re by linarith)

private theorem neg_normalized_re (z : ℂ) :
    (-((2 * Real.pi * I : ℂ)⁻¹ * z)).re = -z.im / (2 * Real.pi) := by
  rw [show (2 * Real.pi * I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * I by push_cast; rfl]
  rw [mul_inv_rev, inv_I, ← ofReal_inv]
  simp only [neg_mul, neg_neg, mul_re, mul_im, I_re, I_im, ofReal_re,
    ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub, neg_mul]
  ring

/-- Schwarz symmetry pairs the horizontal edges of a thin rectangle.
The real part of the negatively normalized boundary integral is the upper
horizontal imaginary integral, divided by `π`, minus the vertical real error. -/
theorem neg_normalized_rectangleBoundaryIntegral_re_eq
    {f : ℂ → ℂ} {a b ε : ℝ}
    (hf : IntervalIntegrable (fun x : ℝ => f (x + ε * I)) volume a b)
    (hconj : ∀ x ∈ Icc a b, f (x + (-ε) * I) = conj (f (x + ε * I)))
    (hab : a ≤ b) :
    (-((2 * Real.pi * I : ℂ)⁻¹ * rectangleBoundaryIntegral f a b (-ε) ε)).re =
      (∫ x in a..b, (f (x + ε * I)).im) / Real.pi -
        ((∫ y in -ε..ε, f (b + y * I)).re -
          (∫ y in -ε..ε, f (a + y * I)).re) / (2 * Real.pi) := by
  have hp : (∫ x in a..b, f (x + (-ε) * I)) =
      conj (∫ x in a..b, f (x + ε * I)) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro x hx
    exact hconj x (by simpa only [uIcc_of_le hab] using hx)
  rw [neg_normalized_re, rectangleBoundaryIntegral]
  simp only [ofReal_neg]
  rw [hp]
  simp only [sub_im, add_im, conj_im, I_mul_im]
  have hi := Complex.imCLM.intervalIntegral_comp_comm hf
  change (∫ x in a..b, (f (x + ε * I)).im) = (∫ x in a..b, f (x + ε * I)).im at hi
  rw [← hi]
  field_simp
  ring

private theorem norm_exp_mul_le {z v : ℂ} {b C : ℝ}
    (hz : z.re ≤ b) (hv : ‖v‖ ≤ C) : ‖exp z * v‖ ≤ Real.exp b * C := by
  rw [norm_mul, norm_exp]
  exact mul_le_mul (Real.exp_le_exp.mpr hz) hv (norm_nonneg _) (Real.exp_pos _).le

private theorem neg_exp_mul_le_im_exp_add_mul {x b ε C : ℝ} {z : ℂ}
    (hx : x ≤ b) (hε : 0 ≤ ε) (hε' : ε ≤ 1) (hC : 0 ≤ C)
    (hz : 0 ≤ z.im) (hnorm : ‖z‖ ≤ C) :
    -(Real.exp b * C * ε) ≤ (exp (x + ε * I) * z).im := by
  have hcos : 0 ≤ Real.cos ε :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos]) (hε'.trans Real.one_le_pi_div_two)
  have hphase := neg_abs_sin_mul_norm_le_im_exp_mul hcos hz
  have hs : |Real.sin ε| ≤ ε := by
    simpa only [abs_of_nonneg hε] using (Real.abs_sin_le_abs (x := ε))
  have hs' : |Real.sin ε| * ‖z‖ ≤ ε * C :=
    mul_le_mul hs hnorm (norm_nonneg _) hε
  have hrot : -(ε * C) ≤ (exp (ε * I) * z).im := by linarith
  have heq : (exp (x + ε * I) * z).im =
      Real.exp x * (exp (ε * I) * z).im := by
    rw [exp_add, mul_assoc]
    simp only [mul_im, exp_ofReal_re, exp_ofReal_im, zero_mul, add_zero]
  rw [heq]
  have h₁ := mul_le_mul_of_nonneg_left hrot (Real.exp_pos x).le
  have h₂ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx)
    (mul_nonneg hε hC)
  nlinarith

/-- A uniformly bounded Schwarz-symmetric function with nonnegative imaginary
part on the upper edge has a negatively normalized exponential contour moment
bounded below by an explicit quantity tending to zero with the rectangle's
height. The vertical estimate uses actual edge integrals and no boundary limits.
This is the scalar error bound in the planar route to `trace-exponential-stahl`. -/
theorem neg_normalized_exp_rectangleBoundaryIntegral_re_ge
    {h : ℂ → ℂ} {a b ε C : ℝ} (hab : a ≤ b)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1)
    (hint : IntervalIntegrable (fun x : ℝ => exp (x + ε * I) * h (x + ε * I))
      volume a b)
    (hconj : ∀ x ∈ Icc a b, h (x + (-ε) * I) = conj (h (x + ε * I)))
    (him : ∀ x ∈ Icc a b, 0 ≤ (h (x + ε * I)).im)
    (hupper : ∀ x ∈ Icc a b, ‖h (x + ε * I)‖ ≤ C)
    (hleft : ∀ y ∈ Icc (-ε) ε, ‖h (a + y * I)‖ ≤ C)
    (hright : ∀ y ∈ Icc (-ε) ε, ‖h (b + y * I)‖ ≤ C) :
    -((b - a + 2) * Real.exp b * C / Real.pi) * ε ≤
      (-((2 * Real.pi * I : ℂ)⁻¹ *
        rectangleBoundaryIntegral (fun z => exp z * h z) a b (-ε) ε)).re := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hupper a ⟨le_rfl, hab⟩)
  have hpair (x : ℝ) (hx : x ∈ Icc a b) :
      exp (x + (-ε) * I) * h (x + (-ε) * I) =
        conj (exp (x + ε * I) * h (x + ε * I)) := by
    rw [map_mul, hconj x hx, ← exp_conj]
    congr 2
    simp
  rw [neg_normalized_rectangleBoundaryIntegral_re_eq hint hpair hab]
  have himint : IntervalIntegrable
      (fun x : ℝ => (exp (x + ε * I) * h (x + ε * I)).im) volume a b :=
    ⟨hint.1.im, hint.2.im⟩
  have hhor := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => -(Real.exp b * C * ε)) volume a b) himint
    (fun x hx => neg_exp_mul_le_im_exp_add_mul hx.2 hε hε' hC
      (him x hx) (hupper x hx))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hhor
  have hv (c : ℝ) (hc : c ≤ b)
      (hn : ∀ y ∈ Icc (-ε) ε, ‖h (c + y * I)‖ ≤ C) :
      ‖∫ y in -ε..ε, exp (c + y * I) * h (c + y * I)‖ ≤
        Real.exp b * C * (2 * ε) := by
    have heps : -ε ≤ ε := by linarith
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -ε) (b := ε) (C := Real.exp b * C) (f := fun y : ℝ =>
        exp (c + y * I) * h (c + y * I)) (fun y hy => by
          apply norm_exp_mul_le (by simpa using hc)
          exact hn y (Ioc_subset_Icc_self (by simpa only [uIoc_of_le heps] using hy)))
    simpa only [sub_neg_eq_add, ← two_mul, abs_of_nonneg (show 0 ≤ 2 * ε by positivity)]
      using hb
  have hvl := hv a hab hleft
  have hvr := hv b le_rfl hright
  have hr := (re_le_norm (∫ y in -ε..ε,
    exp (b + y * I) * h (b + y * I))).trans hvr
  have hl := ((neg_le_abs (∫ y in -ε..ε,
    exp (a + y * I) * h (a + y * I)).re).trans (abs_re_le_norm _)).trans hvl
  generalize (∫ x in a..b, (exp (x + ε * I) * h (x + ε * I)).im) = H at *
  generalize (∫ y in -ε..ε, exp (b + y * I) * h (b + y * I)).re = Vr at *
  generalize (∫ y in -ε..ε, exp (a + y * I) * h (a + y * I)).re = Vl at *
  have hpi := Real.pi_pos
  apply (mul_le_mul_iff_of_pos_right hpi).mp
  field_simp
  nlinarith

/-- A fixed contour moment represented by all sufficiently thin rectangles is
nonnegative when the upper-half-plane function has nonnegative imaginary part,
is uniformly bounded near the real segment, and satisfies Schwarz reflection
on the horizontal edges. The contour-identification premise is explicit: this
theorem supplies the scalar positivity step, independently of its matrix bridge.
No real-axis root limits or boundary value theorem are required. -/
theorem nonneg_of_neg_normalized_exp_rectangleBoundaryIntegral_re_eq
    {h : ℂ → ℂ} {a b C δ w : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hcont : ∀ ε ∈ Ioo 0 δ,
      ContinuousOn (fun x : ℝ => h (x + ε * I)) (Icc a b))
    (hconj : ∀ ε ∈ Ioo 0 δ, ∀ x ∈ Icc a b,
      h (x + (-ε) * I) = conj (h (x + ε * I)))
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc (-δ) δ, ‖h (x + y * I)‖ ≤ C)
    (hw : ∀ ε ∈ Ioo 0 δ,
      (-((2 * Real.pi * I : ℂ)⁻¹ *
        rectangleBoundaryIntegral (fun z => exp z * h z) a b (-ε) ε)).re = w) :
    0 ≤ w := by
  let K : ℝ := (b - a + 2) * Real.exp b * C / Real.pi
  have hest : ∀ᶠ ε in 𝓝[>] (0 : ℝ), -K * ε ≤ w := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ zero_lt_one)] with ε hε
    have heδ : ε ∈ Ioo 0 δ := ⟨hε.1, (lt_min_iff.mp hε.2).1⟩
    have he1 : ε ≤ 1 := (lt_min_iff.mp hε.2).2.le
    have hebox : ε ∈ Icc (-δ) δ := ⟨by linarith [heδ.1], heδ.2.le⟩
    rw [← hw ε heδ]
    apply neg_normalized_exp_rectangleBoundaryIntegral_re_ge hab hε.1.le he1
    · exact ((by fun_prop : ContinuousOn (fun x : ℝ => exp (x + ε * I))
        (Icc a b)).mul (hcont ε heδ)).intervalIntegrable_of_Icc hab
    · exact hconj ε heδ
    · intro x _
      apply him
      simpa using hε.1
    · intro x hx
      exact hbound x hx ε hebox
    · intro y hy
      exact hbound a ⟨le_rfl, hab⟩ y ⟨by linarith [heδ.2, hy.1], by linarith [heδ.2, hy.2]⟩
    · intro y hy
      exact hbound b ⟨hab, le_rfl⟩ y ⟨by linarith [heδ.2, hy.1], by linarith [heδ.2, hy.2]⟩
  have hlim : Tendsto (fun ε : ℝ => -K * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_const_nhds.mul ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)))
  exact le_of_tendsto hlim hest

/-- Thin rectangular contour integrals are independent of their height when
the integrand is holomorphic off the real axis and continuous along the two
vertical edges. The real segment inside the rectangle may contain a jump or
branch cut. This is a direct planar Cauchy deformation, with no boundary values
on that segment assumed. -/
theorem rectangleBoundaryIntegral_eq_of_differentiableOn_off_real
    {f : ℂ → ℂ} {a b ε η : ℝ} (hε : 0 < ε) (hεη : ε ≤ η)
    (hf : DifferentiableOn ℂ f {z | z.im ≠ 0})
    (hleft : ContinuousOn (fun y : ℝ => f (a + y * I)) (Icc (-η) η))
    (hright : ContinuousOn (fun y : ℝ => f (b + y * I)) (Icc (-η) η)) :
    rectangleBoundaryIntegral f a b (-ε) ε =
      rectangleBoundaryIntegral f a b (-η) η := by
  have hη : 0 < η := hε.trans_le hεη
  have hup : rectangleBoundaryIntegral f a b ε η = 0 := by
    have hd : DifferentiableOn ℂ f
        ([[((a : ℂ) + ε * I).re, ((b : ℂ) + η * I).re]] ×ℂ
          [[((a : ℂ) + ε * I).im, ((b : ℂ) + η * I).im]]) := by
      apply hf.mono
      intro z hz
      have hi : z.im ∈ Icc ε η := by
        simpa [uIcc_of_le hεη] using hz.2
      exact ne_of_gt (hε.trans_le hi.1)
    simpa [rectangleBoundaryIntegral, smul_eq_mul] using
      integral_boundary_rect_eq_zero_of_differentiableOn f
        ((a : ℂ) + ε * I) ((b : ℂ) + η * I) hd
  have hlo : rectangleBoundaryIntegral f a b (-η) (-ε) = 0 := by
    have hd : DifferentiableOn ℂ f
        ([[((a : ℂ) + (-η) * I).re, ((b : ℂ) + (-ε) * I).re]] ×ℂ
          [[((a : ℂ) + (-η) * I).im, ((b : ℂ) + (-ε) * I).im]]) := by
      apply hf.mono
      intro z hz
      have hi : z.im ∈ Icc (-η) (-ε) := by
        simpa [uIcc_of_le (neg_le_neg hεη)] using hz.2
      exact ne_of_lt (hi.2.trans_lt (neg_neg_of_pos hε))
    simpa [rectangleBoundaryIntegral, smul_eq_mul] using
      integral_boundary_rect_eq_zero_of_differentiableOn f
        ((a : ℂ) + (-η) * I) ((b : ℂ) + (-ε) * I) hd
  have hsplit (r : ℝ)
      (hr : ContinuousOn (fun y : ℝ => f (r + y * I)) (Icc (-η) η)) :
      (∫ y in -η..η, f (r + y * I)) =
        (∫ y in -η..-ε, f (r + y * I)) +
          (∫ y in -ε..ε, f (r + y * I)) +
            (∫ y in ε..η, f (r + y * I)) := by
    have hall : IntervalIntegrable (fun y : ℝ => f (r + y * I)) volume (-η) η :=
      hr.intervalIntegrable_of_Icc (by linarith : -η ≤ η)
    have hpart (u v : ℝ) (hu : -η ≤ u) (hv : v ≤ η) (huv : u ≤ v) :
        IntervalIntegrable (fun y : ℝ => f (r + y * I)) volume u v := by
      apply hall.mono_set
      simpa only [uIcc_of_le huv, uIcc_of_le (show -η ≤ η by linarith)] using
        (Icc_subset_Icc hu hv)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hpart (-η) ε le_rfl hεη (by linarith))
      (hpart ε η (by linarith) le_rfl hεη)]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hpart (-η) (-ε) le_rfl (by linarith) (by linarith))
      (hpart (-ε) ε (by linarith) hεη (by linarith))]
  have hsum : rectangleBoundaryIntegral f a b (-η) η =
      rectangleBoundaryIntegral f a b (-ε) ε +
        rectangleBoundaryIntegral f a b ε η +
          rectangleBoundaryIntegral f a b (-η) (-ε) := by
    simp only [rectangleBoundaryIntegral]
    rw [hsplit b hright, hsplit a hleft]
    ring
  simpa only [hup, hlo, add_zero] using hsum.symm

/-- A Schwarz-symmetric function holomorphic off the real axis, with
nonnegative imaginary part in the upper half-plane and a uniform bound in a
rectangle, has a nonnegative negatively normalized exponential boundary moment.
Only the vertical sides need continuity across the real axis. Cauchy deformation
to thin rectangles and the vanishing quantitative error are proved here.
This supplies the complete scalar thin-rectangle positivity step for the planar
root-sum route to atlas `trace-exponential-stahl`; the matrix-to-contour bridge
remains independent. -/
theorem neg_normalized_exp_rectangleBoundaryIntegral_re_nonneg
    {h : ℂ → ℂ} {a b C δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hh : DifferentiableOn ℂ h {z | z.im ≠ 0})
    (hleft : ContinuousOn (fun y : ℝ => h (a + y * I)) (Icc (-δ) δ))
    (hright : ContinuousOn (fun y : ℝ => h (b + y * I)) (Icc (-δ) δ))
    (hconj : ∀ z : ℂ, z.im ≠ 0 → h (conj z) = conj (h z))
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc (-δ) δ, ‖h (x + y * I)‖ ≤ C) :
    0 ≤ (-((2 * Real.pi * I : ℂ)⁻¹ *
      rectangleBoundaryIntegral (fun z => exp z * h z) a b (-δ) δ)).re := by
  have hf : DifferentiableOn ℂ (fun z => exp z * h z) {z | z.im ≠ 0} :=
    differentiable_exp.differentiableOn.mul hh
  have hfl : ContinuousOn (fun y : ℝ => exp (a + y * I) * h (a + y * I))
      (Icc (-δ) δ) := (by fun_prop : ContinuousOn
        (fun y : ℝ => exp (a + y * I)) (Icc (-δ) δ)).mul hleft
  have hfr : ContinuousOn (fun y : ℝ => exp (b + y * I) * h (b + y * I))
      (Icc (-δ) δ) := (by fun_prop : ContinuousOn
        (fun y : ℝ => exp (b + y * I)) (Icc (-δ) δ)).mul hright
  apply nonneg_of_neg_normalized_exp_rectangleBoundaryIntegral_re_eq hab hδ
  · intro ε hε
    apply hh.continuousOn.comp (by fun_prop)
    intro x _
    simpa using (ne_of_gt hε.1)
  · intro ε hε x _
    simpa using hconj (x + ε * I) (by simpa using (ne_of_gt hε.1))
  · exact him
  · exact hbound
  · intro ε hε
    rw [rectangleBoundaryIntegral_eq_of_differentiableOn_off_real hε.1 hε.2.le hf hfl hfr]

end Complex
