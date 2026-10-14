import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Small complex sine coordinates

Every point of the complex disk of radius one half has a sine preimage with
controlled norm and imaginary part. The construction uses only real inverse
sine and inverse hyperbolic sine and finite real algebra.
-/

noncomputable section

open Set

namespace Real

/-- In the interval of radius one half, inverse sine increases absolute value by
at most a factor of two. -/
theorem abs_arcsin_le_two_mul_abs {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |arcsin x| ≤ 2 * |x| := by
  have hd (y : ℝ) (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      HasDerivWithinAt arcsin (1 / sqrt (1 - y^2))
        (Icc (-(1 / 2 : ℝ)) (1 / 2)) y :=
    (hasDerivAt_arcsin (by linarith [hy.1]) (by linarith [hy.2])).hasDerivWithinAt
  have hb (y : ℝ) (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      ‖1 / sqrt (1 - y^2)‖ ≤ 2 := by
    have hy2 : y^2 ≤ 1 / 4 := by nlinarith [hy.1, hy.2]
    have hs : 0 < sqrt (1 - y^2) := sqrt_pos.mpr (by linarith)
    have hsq := sq_sqrt (by linarith : 0 ≤ 1 - y^2)
    rw [norm_eq_abs, abs_of_pos (one_div_pos.mpr hs)]
    apply (div_le_iff₀ hs).mpr
    nlinarith
  have h := (convex_Icc (-(1 / 2 : ℝ)) (1 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := 0) (y := x) hd hb (by constructor <;> norm_num) (abs_le.mp hx)
  simpa only [arcsin_zero, sub_zero, norm_eq_abs] using h

/-- Inverse hyperbolic sine is bounded above by its nonnegative argument. -/
theorem arsinh_le_self {x : ℝ} (hx : 0 ≤ x) : arsinh x ≤ x := by
  calc
    arsinh x ≤ sinh (arsinh x) := self_le_sinh_iff.mpr (arsinh_nonneg_iff.mpr hx)
    _ = x := sinh_arsinh x

end Real

namespace Complex

private theorem exists_small_sin_coordinates_upper {x y r : ℝ}
    (hy : 0 ≤ y) (hr : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (hxy : x^2 + y^2 = r^2) :
    ∃ a b : ℝ, Real.sin a * Real.cosh b = x ∧
      Real.cos a * Real.sinh b = y ∧
      |a| ≤ 2 * |x| ∧ 0 ≤ b ∧
      b ≤ y / Real.sqrt (1 - r^2) ∧ b ≤ 2 * y := by
  let d := 1 - r^2
  let v := (Real.sqrt (d^2 + 4*y^2) - d) / 2
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hr2 : r^2 ≤ 1 / 4 := by nlinarith
  have hv : 0 ≤ v := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ d^2 + 4*y^2)
    have hsn := Real.sqrt_nonneg (d^2 + 4*y^2)
    dsimp [v]
    nlinarith
  have hveq : v * (v + d) = y^2 := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ d^2 + 4*y^2)
    dsimp [v]
    nlinarith
  have hvle : v ≤ y^2 / d := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg v]
  have hroot : 0 < Real.sqrt (1 + v) := Real.sqrt_pos.mpr (by linarith)
  have hrootsq := Real.sq_sqrt (by linarith : 0 ≤ 1 + v)
  have hrootge : 1 ≤ Real.sqrt (1 + v) := by nlinarith
  have hxle : |x| ≤ 1 / 2 := by
    have hxsq : x^2 ≤ 1 / 4 := by nlinarith [sq_nonneg y]
    rw [← sq_abs x] at hxsq
    nlinarith [abs_nonneg x]
  have hquot : |x / Real.sqrt (1 + v)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hroot]
    exact (div_le_self (abs_nonneg x) hrootge).trans hxle
  let a := Real.arcsin (x / Real.sqrt (1 + v))
  let b := Real.arsinh (Real.sqrt v)
  have hsa : Real.sin a = x / Real.sqrt (1 + v) :=
    Real.sin_arcsin (by linarith [(abs_le.mp hquot).1])
      (by linarith [(abs_le.mp hquot).2])
  have hcb : Real.cosh b = Real.sqrt (1 + v) := by
    dsimp [b]
    rw [Real.cosh_arsinh, Real.sq_sqrt hv]
  have hsb : Real.sinh b = Real.sqrt v := Real.sinh_arsinh _
  have hca : 0 ≤ Real.cos a := Real.cos_arcsin_nonneg _
  have hcq : (Real.cos a)^2 = 1 - x^2 / (1 + v) := by
    have h := Real.sin_sq_add_cos_sq a
    rw [hsa, div_pow, hrootsq] at h
    linarith
  have hcy : Real.cos a * Real.sqrt v = y := by
    have hsq : (Real.cos a * Real.sqrt v)^2 = y^2 := by
      rw [mul_pow, Real.sq_sqrt hv, hcq]
      have hpos : 1 + v ≠ 0 := by positivity
      field_simp [hpos]
      dsimp [d] at hveq
      nlinarith
    have hn : 0 ≤ Real.cos a * Real.sqrt v := mul_nonneg hca (Real.sqrt_nonneg v)
    nlinarith
  have hbn : 0 ≤ b := Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg v)
  have hble : b ≤ Real.sqrt v := Real.arsinh_le_self (Real.sqrt_nonneg v)
  have hsqrtd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hvsqrt : Real.sqrt v ≤ y / Real.sqrt d := by
    have hsq := Real.sq_sqrt hv
    have hdsq := Real.sq_sqrt hd.le
    have hp : 0 ≤ y / Real.sqrt d := div_nonneg hy hsqrtd.le
    have hdivsq : v ≤ (y / Real.sqrt d)^2 := by
      rwa [div_pow, hdsq]
    nlinarith [Real.sqrt_nonneg v]
  have hds : 1 / 2 ≤ Real.sqrt d := by
    have hdsq := Real.sq_sqrt hd.le
    have hn := Real.sqrt_nonneg d
    dsimp [d] at hdsq
    nlinarith
  have hquotabs : |x / Real.sqrt (1 + v)| ≤ |x| := by
    rw [abs_div, abs_of_pos hroot]
    exact div_le_self (abs_nonneg x) hrootge
  refine ⟨a, b, ?_, ?_, ?_, hbn, ?_, ?_⟩
  · rw [hsa, hcb, div_mul_cancel₀ _ hroot.ne']
  · rw [hsb, hcy]
  · exact (Real.abs_arcsin_le_two_mul_abs hquot).trans
      (mul_le_mul_of_nonneg_left hquotabs (by norm_num))
  · exact hble.trans hvsqrt
  · refine hble.trans (hvsqrt.trans ?_)
    apply (div_le_iff₀ hsqrtd).mpr
    nlinarith

/-- A complex point in the disk of radius one half has a sine preimage of norm
at most twice its norm, whose imaginary part is controlled by the point's
imaginary part. The construction uses real inverse functions.
Source: the focused polynomial Bernstein reroute, sine-coordinate lemma. -/
theorem exists_sin_eq_of_norm_le_half {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ∃ u : ℂ, sin u = z ∧ ‖u‖ ≤ 2 * ‖z‖ ∧
      |u.im| ≤ |z.im| / Real.sqrt (1 - ‖z‖^2) := by
  have hxy : z.re^2 + |z.im|^2 = ‖z‖^2 := by
    rw [sq_abs, ← normSq_eq_norm_sq, normSq_apply]
    ring
  obtain ⟨a, b, hre, him, ha, hb, hble, hb2⟩ := exists_small_sin_coordinates_upper
    (abs_nonneg z.im) (norm_nonneg z) hz hxy
  let u : ℂ := ⟨a, if 0 ≤ z.im then b else -b⟩
  have hum : |u.im| = b := by
    dsimp [u]
    split_ifs
    · exact abs_of_nonneg hb
    · rw [abs_neg, abs_of_nonneg hb]
  have husq : ‖u‖^2 = a^2 + b^2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    change a * a + (if 0 ≤ z.im then b else -b) *
      (if 0 ≤ z.im then b else -b) = a^2 + b^2
    split_ifs <;> ring
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [sin_eq]
    simp only [← ofReal_sin, ← ofReal_cosh, ← ofReal_cos, ← ofReal_sinh]
    apply Complex.ext
    · simp only [u, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im,
        add_re, mul_zero, sub_zero, zero_mul, sub_self, add_zero]
      split_ifs
      · exact hre
      · simpa only [Real.cosh_neg] using hre
    · simp only [u, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im,
        add_im, mul_zero, sub_zero, zero_mul, add_zero, zero_add, mul_one]
      split_ifs with hy
      · simpa only [abs_of_nonneg hy] using him
      · rw [Real.sinh_neg, mul_neg, him, abs_of_neg (lt_of_not_ge hy), neg_neg]
  · have hasq : a^2 ≤ (2 * |z.re|)^2 := by
      rw [← sq_abs a]
      exact pow_le_pow_left₀ (abs_nonneg a) ha 2
    have hbsq : b^2 ≤ (2 * |z.im|)^2 := pow_le_pow_left₀ hb hb2 2
    have hzsq : z.re^2 + z.im^2 = ‖z‖^2 := by simpa only [sq_abs] using hxy
    simp only [mul_pow, sq_abs] at hasq hbsq
    nlinarith [norm_nonneg u, norm_nonneg z]
  · rw [hum]
    exact hble

end Complex
