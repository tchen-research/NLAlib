import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Sign

/-!
# Odd sine series and Abel limits

Finite trigonometric telescopes bound odd sine partial sums. Dirichlet's test
and the complex arctangent power series identify their damped radial sums.
-/

noncomputable section

open Real Finset Set Filter
open scoped Topology ComplexConjugate

namespace NLAlib

/-- An odd sine partial sum is an exact trigonometric telescope.
Source: finite product-to-sum; helper for `chebyshev-series-abs-sign`. -/
theorem sum_sin_odd_eq (φ : ℝ) (hφ : Real.sin φ ≠ 0) (n : ℕ) :
    (∑ j ∈ range n, Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ)) =
      Real.sin ((n : ℝ) * φ) ^ 2 / Real.sin φ := by
  have hterm : ∀ j : ℕ, 2 * Real.sin φ * Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ) =
      Real.cos ((2 * j : ℕ) * φ) - Real.cos ((2 * (j + 1) : ℕ) * φ) := by
    intro j
    have hm : ((2 * j : ℕ) : ℝ) * φ = (((2 * j + 1 : ℕ) : ℝ) * φ) - φ := by push_cast; ring
    have hp : ((2 * (j + 1) : ℕ) : ℝ) * φ = (((2 * j + 1 : ℕ) : ℝ) * φ) + φ := by push_cast; ring
    rw [hm, hp, Real.cos_sub, Real.cos_add]
    ring
  have hsum : 2 * Real.sin φ * (∑ j ∈ range n, Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ)) =
      2 * Real.sin ((n : ℝ) * φ) ^ 2 := by
    rw [mul_sum]
    simp_rw [hterm]
    rw [sum_range_sub']
    rw [show ((2 * n : ℕ) : ℝ) * φ = 2 * ((n : ℝ) * φ) by push_cast; ring,
      Real.cos_two_mul_eq_one_sub]
    simp only [Nat.mul_zero, Nat.cast_zero, zero_mul, Real.cos_zero]
    ring
  apply (eq_div_iff hφ).mpr
  nlinarith

/-- The odd sine partial sums have the uniform Dirichlet bound `1/|sin φ|`.
Source: finite sine telescope; helper for `chebyshev-series-abs-sign`. -/
theorem norm_sum_sin_odd_le (φ : ℝ) (hφ : Real.sin φ ≠ 0) (n : ℕ) :
    ‖∑ j ∈ range n, Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ)‖ ≤ 1 / |Real.sin φ| := by
  rw [Real.norm_eq_abs, sum_sin_odd_eq φ hφ, abs_div, abs_of_nonneg (sq_nonneg _)]
  exact div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (abs_nonneg _)

/-- The reciprocal odd integers tend to zero.
Source: elementary real reciprocal limit; helper for `chebyshev-series-abs-sign`. -/
theorem tendsto_one_div_odd_atTop :
    Tendsto (fun j : ℕ => 1 / (2 * (j : ℝ) + 1)) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun j => by positivity))
    _ (show Tendsto (fun j : ℕ => (j : ℝ)⁻¹) atTop (𝓝 0) from tendsto_inv_atTop_nhds_zero_nat)
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  simpa only [one_div] using one_div_le_one_div_of_le hjR
    (show (j : ℝ) ≤ 2 * j + 1 by nlinarith [Nat.cast_nonneg (α := ℝ) j])

/-- The odd sine harmonic series converges in its ordinary partial-sum order away from zero.
Source: Dirichlet's test; helper for `chebyshev-series-abs-sign`. -/
theorem exists_tendsto_sum_sin_odd_div (φ : ℝ) (hφ : Real.sin φ ≠ 0) :
    ∃ L : ℝ, Tendsto (fun n => ∑ j ∈ range n,
      Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ) / (2 * (j : ℝ) + 1)) atTop (𝓝 L) := by
  have hanti : Antitone (fun j : ℕ => 1 / (2 * (j : ℝ) + 1)) := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (show 2 * i + 1 ≤ 2 * j + 1 by omega))
  have hC := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded tendsto_one_div_odd_atTop
    (norm_sum_sin_odd_le φ hφ)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨L, ?_⟩
  simpa only [smul_eq_mul, one_div, mul_comm _ (Real.sin _), ← div_eq_mul_inv] using hL

/-- Radial damping of the odd sine series is the real part of a complex arctangent.
Source: Mathlib's actual complex arctangent power series; helper for `chebyshev-series-abs-sign`. -/
theorem hasSum_pow_mul_sin_odd_div (φ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun j : ℕ => r ^ (2 * j + 1) * Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ) /
      (2 * (j : ℝ) + 1)) (-(Complex.arctan (Complex.I * (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).re) := by
  let w : ℂ := Complex.exp ((φ : ℂ) * Complex.I)
  have hw : ‖w‖ = 1 := by dsimp [w]; simp [Complex.norm_exp]
  have hz : ‖Complex.I * (r : ℂ) * w‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, hw]
    simpa using hr1
  have hs := Complex.reCLM.hasSum (Complex.hasSum_arctan hz)
  have hterm : ∀ j : ℕ,
      (((-1 : ℂ) ^ j * (Complex.I * (r : ℂ) * w) ^ (2 * j + 1) /
        ((2 * j + 1 : ℕ) : ℂ)).re) =
          -(r ^ (2 * j + 1) * Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ) / (2 * (j : ℝ) + 1)) := by
    intro j
    have hi : (-1 : ℂ) ^ j * Complex.I ^ (2 * j + 1) = Complex.I := by
      rw [pow_add, pow_mul, Complex.I_sq]
      simp only [pow_one]
      rw [← mul_assoc, ← mul_pow]
      norm_num
    have heq : (-1 : ℂ) ^ j * (Complex.I * (r : ℂ) * w) ^ (2 * j + 1) =
        Complex.I * (r : ℂ) ^ (2 * j + 1) * w ^ (2 * j + 1) := by
      rw [mul_pow, mul_pow]
      calc _ = ((-1 : ℂ) ^ j * Complex.I ^ (2 * j + 1)) * (r : ℂ) ^ (2 * j + 1) * w ^ (2 * j + 1) := by ring
        _ = _ := by rw [hi]
    rw [heq]
    have him : (w ^ (2 * j + 1)).im = Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ) := by
      dsimp only [w]
      rw [← Complex.exp_nat_mul]
      have he : ((2 * j + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I) =
          ((((2 * j + 1 : ℕ) : ℝ) * φ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [he, Complex.exp_ofReal_mul_I_im]
    rw [show ((2 * j + 1 : ℕ) : ℂ) = ((2 * (j : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_pow, Complex.div_ofReal_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, him, zero_mul, mul_zero, zero_add,
      sub_zero, zero_sub, one_mul]
    ring
  change HasSum (fun j : ℕ =>
    (((-1 : ℂ) ^ j * (Complex.I * (r : ℂ) * w) ^ (2 * j + 1) /
      ((2 * j + 1 : ℕ) : ℂ)).re)) (Complex.arctan (Complex.I * (r : ℂ) * w)).re at hs
  simp_rw [hterm] at hs
  simpa only [neg_neg] using hs.neg

/-- The Cayley quotient of a nonreal unit point has zero real part and the opposite imaginary sign.
Source: elementary unit-circle algebra; helper for `chebyshev-series-abs-sign`. -/
theorem re_im_unit_circle_cayley {w : ℂ} (hw : ‖w‖ = 1) (hi : w.im ≠ 0) :
    ((1 - w) / (1 + w)).re = 0 ∧
      ((1 - w) / (1 + w)).im = -2 * w.im / Complex.normSq (1 + w) ∧
      0 < Complex.normSq (1 + w) := by
  have hne : (1 : ℂ) + w ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, Complex.zero_im, zero_add] at him
    exact hi him
  have hn : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw]; norm_num
  have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, ← pow_two] using hn
  refine ⟨?_, ?_, Complex.normSq_pos.mpr hne⟩
  · rw [Complex.div_re]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im,
      Complex.add_im, Complex.one_im, zero_sub, zero_add]
    rw [← add_div, show (1 - w.re) * (1 + w.re) + -w.im * w.im = 0 by nlinarith [hsq], zero_div]
  · rw [Complex.div_im]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im,
      Complex.add_im, Complex.one_im, zero_sub, zero_add]
    rw [← sub_div]
    congr 1
    ring

/-- The endpoint arctangent value of a nonreal unit-circle point gives the square-wave sign.
Source: the principal complex logarithm and Cayley transform;
helper for `chebyshev-series-abs-sign`. -/
theorem neg_re_arctan_I_mul_eq_sign {w : ℂ} (hw : ‖w‖ = 1) (hi : w.im ≠ 0) :
    -(Complex.arctan (Complex.I * w)).re = Real.pi / 4 * Real.sign w.im := by
  let q : ℂ := (1 - w) / (1 + w)
  obtain ⟨hqr, hqi, hd⟩ := re_im_unit_circle_cayley hw hi
  have hI : Complex.I * w * Complex.I = -w := by
    calc Complex.I * w * Complex.I = w * (Complex.I * Complex.I) := by ring
      _ = -w := by rw [Complex.I_mul_I]; simp
  have harctan : (Complex.arctan (Complex.I * w)).re = q.arg / 2 := by
    rw [Complex.arctan, hI, ← sub_eq_add_neg, sub_neg_eq_add]
    change (-Complex.I / 2 * Complex.log q).re = q.arg / 2
    norm_num [Complex.mul_re]
    rw [Complex.log_im]
    ring
  rw [harctan]
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · have hqpos : 0 < q.im := by
      change 0 < ((1 - w) / (1 + w)).im
      rw [hqi]
      exact div_pos (by linarith) hd
    rw [Complex.arg_eq_pi_div_two_iff.mpr ⟨hqr, hqpos⟩, Real.sign_of_neg hneg]
    ring
  · have hqneg : q.im < 0 := by
      change ((1 - w) / (1 + w)).im < 0
      rw [hqi]
      exact div_neg_of_neg_of_pos (by linarith) hd
    rw [Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hqr, hqneg⟩, Real.sign_of_pos hpos]
    ring

/-- Radial arctangent evaluation is continuous at a nonreal unit-circle endpoint.
Source: continuity of the principal logarithm away from its cut;
helper for `chebyshev-series-abs-sign`. -/
theorem continuousAt_neg_re_arctan_I_mul {w : ℂ} (hw : ‖w‖ = 1) (hi : w.im ≠ 0) :
    ContinuousAt (fun r : ℝ => -(Complex.arctan (Complex.I * (r : ℂ) * w)).re) 1 := by
  obtain ⟨hqr, hqi, hd⟩ := re_im_unit_circle_cayley hw hi
  have hqne : ((1 - w) / (1 + w)).im ≠ 0 := by
    rw [hqi]
    exact div_ne_zero (mul_ne_zero (by norm_num) hi) hd.ne'
  have hI : Complex.I * w * Complex.I = -w := by
    calc Complex.I * w * Complex.I = w * (Complex.I * Complex.I) := by ring
      _ = -w := by rw [Complex.I_mul_I]; simp
  have hden : (1 : ℂ) - Complex.I * (1 : ℂ) * w * Complex.I ≠ 0 := by
    simp only [mul_one, hI, sub_neg_eq_add]
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, Complex.zero_im, zero_add] at him
    exact hi him
  have hq : ((1 + Complex.I * (1 : ℂ) * w * Complex.I) /
      (1 - Complex.I * (1 : ℂ) * w * Complex.I)) ∈ Complex.slitPlane := by
    simp only [mul_one, hI, ← sub_eq_add_neg, sub_neg_eq_add]
    exact Complex.mem_slitPlane_iff.mpr (Or.inr hqne)
  have hquot : ContinuousAt (fun r : ℝ =>
      (1 + Complex.I * (r : ℂ) * w * Complex.I) /
        (1 - Complex.I * (r : ℂ) * w * Complex.I)) 1 :=
    (by fun_prop : ContinuousAt (fun r : ℝ => 1 + Complex.I * (r : ℂ) * w * Complex.I) 1).div
      (by fun_prop) hden
  have hlog := hquot.clog hq
  have harctan := hlog.const_mul (-Complex.I / 2)
  exact (Complex.continuous_re.continuousAt.comp harctan).neg

/-- The odd sine harmonic series has the ordinary square-wave value.
Source: Dirichlet's test, Abel's limit theorem, and the genuine arctangent power series;
helper for `chebyshev-series-abs-sign`. -/
theorem tendsto_sum_sin_odd_div (φ : ℝ) (hφ : Real.sin φ ≠ 0) :
    Tendsto (fun n => ∑ j ∈ range n,
      Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ) / (2 * (j : ℝ) + 1)) atTop
      (𝓝 (Real.pi / 4 * Real.sign (Real.sin φ))) := by
  obtain ⟨L, hL⟩ := exists_tendsto_sum_sin_odd_div φ hφ
  let w : ℂ := Complex.exp ((φ : ℂ) * Complex.I)
  have hw : ‖w‖ = 1 := by dsimp [w]; simp [Complex.norm_exp]
  have him : w.im = Real.sin φ := Complex.exp_ofReal_mul_I_im φ
  have hine : w.im ≠ 0 := by rwa [him]
  let l : Filter ℝ := 𝓝[Ioo (0 : ℝ) 1] 1
  have hradial : Tendsto (fun r : ℝ => r ^ 2) l (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have ht : Tendsto (fun r : ℝ => r ^ 2) (𝓝 (1 : ℝ)) (𝓝 (1 : ℝ)) := by
        have hc : ContinuousAt (fun r : ℝ => r ^ 2) (1 : ℝ) := by fun_prop
        simpa only [one_pow] using hc.tendsto
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change r ^ 2 < 1
      nlinarith [hr.1, hr.2]
  have hAbel := (Real.tendsto_tsum_powerSeries_nhdsWithin_lt hL).comp hradial
  have hid : Tendsto (fun r : ℝ => r) l (𝓝 (1 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hmul := hid.mul hAbel
  simp only [one_mul] at hmul
  have hF : Tendsto (fun r : ℝ => -(Complex.arctan (Complex.I * (r : ℂ) * w)).re) l (𝓝 L) := by
    apply hmul.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hs := hasSum_pow_mul_sin_odd_div φ r hr.1.le hr.2
    change r * (∑' j : ℕ, Real.sin (((2 * j + 1 : ℕ) : ℝ) * φ) /
      (2 * (j : ℝ) + 1) * (r ^ 2) ^ j) = _
    rw [← hs.tsum_eq, ← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [← pow_mul, pow_succ]
    ring
  have hcont : Tendsto (fun r : ℝ => -(Complex.arctan (Complex.I * (r : ℂ) * w)).re) l
      (𝓝 (-(Complex.arctan (Complex.I * (1 : ℂ) * w)).re)) :=
    (continuousAt_neg_re_arctan_I_mul hw hine).tendsto.mono_left nhdsWithin_le_nhds
  have hvalue : -(Complex.arctan (Complex.I * (1 : ℂ) * w)).re =
      Real.pi / 4 * Real.sign (Real.sin φ) := by
    simpa only [mul_one, him] using neg_re_arctan_I_mul_eq_sign hw hine
  rw [hvalue] at hcont
  let : NeBot l := by
    dsimp [l]
    exact right_nhdsWithin_Ioo_neBot (show (0 : ℝ) < 1 by norm_num)
  have heq := tendsto_nhds_unique hF hcont
  rw [heq] at hL
  exact hL

end NLAlib
