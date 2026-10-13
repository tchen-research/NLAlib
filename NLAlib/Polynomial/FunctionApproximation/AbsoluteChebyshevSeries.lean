import NLAlib.Polynomial.FunctionApproximation.ChebyshevLipschitz
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Explicit Chebyshev coefficients of absolute value

Cosine reflection and elementary product-to-sum integration give the even
absolute-value coefficients and the vanishing odd coefficients.
Atlas: `chebyshev-series-abs-sign`.
-/

noncomputable section

set_option maxHeartbeats 600000

open Polynomial Polynomial.Chebyshev Finset Real Set Filter
open scoped Topology

namespace NLAlib

/-- Integrating a nonzero cosine frequency over the positive half period.
Source: elementary trigonometric integration; helper for `chebyshev-series-abs-sign`. -/
theorem integral_cos_mul_half_pi (c : ℝ) (hc : c ≠ 0) :
    (∫ θ in 0..Real.pi / 2, Real.cos (c * θ)) = Real.sin (c * (Real.pi / 2)) / c := by
  rw [intervalIntegral.integral_comp_mul_left _ hc, integral_cos]
  simp [div_eq_mul_inv, mul_comm]

/-- Reflecting the absolute-cosine coefficient integral reduces it to half a period.
Source: Trefethen, ATAP, Exercise 3.6; helper for `chebyshev-series-abs-sign`. -/
theorem chebyshevCoeff_abs_eq_half_integral (k : ℕ) :
    chebyshevCoeff (fun x : ℝ => |x|) k =
      (if k = 0 then 1 else 2) / Real.pi * (1 + (-1 : ℝ) ^ k) *
        ∫ θ in 0..Real.pi / 2, Real.cos θ * Real.cos ((k : ℝ) * θ) := by
  let u : ℝ → ℝ := fun θ => |Real.cos θ| * Real.cos ((k : ℝ) * θ)
  have hu : Continuous u := by fun_prop
  have hsym : ∀ θ, u (Real.pi - θ) = (-1 : ℝ) ^ k * u θ := by
    intro θ
    dsimp only [u]
    rw [Real.cos_pi_sub, abs_neg,
      show (k : ℝ) * (Real.pi - θ) = (k : ℝ) * Real.pi - (k : ℝ) * θ by ring,
      Real.cos_nat_mul_pi_sub]
    ring
  have hreflect : (∫ θ in Real.pi / 2..Real.pi, u θ) =
      (-1 : ℝ) ^ k * ∫ θ in 0..Real.pi / 2, u θ := by
    have h := intervalIntegral.integral_comp_sub_left (f := u) (a := 0) (b := Real.pi / 2) Real.pi
    have hhalf : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
    simp only [hhalf, sub_zero, hsym] at h
    rw [intervalIntegral.integral_const_mul] at h
    exact h.symm
  have hfirst : (∫ θ in 0..Real.pi / 2, u θ) =
      ∫ θ in 0..Real.pi / 2, Real.cos θ * Real.cos ((k : ℝ) * θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have ht : θ ∈ Icc 0 (Real.pi / 2) := by simpa [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
    dsimp only [u]
    rw [abs_of_nonneg (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [ht.1, Real.pi_pos]) ht.2)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hu.intervalIntegrable 0 (Real.pi / 2)) (hu.intervalIntegrable (Real.pi / 2) Real.pi)
  rw [chebyshevCoeff_eq_cosine_integral]
  change (if k = 0 then 1 else 2) / Real.pi * (∫ θ in 0..Real.pi, u θ) = _
  rw [← hsplit, hreflect, hfirst]
  ring

/-- The constant Chebyshev coefficient of absolute value is `2/π`.
Source: Trefethen, ATAP, Exercise 3.6.
atlas: chebyshev-series-abs-sign (partial) -/
@[simp] theorem chebyshevCoeff_abs_zero : chebyshevCoeff (fun x : ℝ => |x|) 0 = 2 / Real.pi := by
  rw [chebyshevCoeff_abs_eq_half_integral]
  simp [integral_cos]
  ring

/-- Every odd Chebyshev coefficient of absolute value vanishes.
Source: Trefethen, ATAP, Exercise 3.6.
atlas: chebyshev-series-abs-sign (partial) -/
@[simp] theorem chebyshevCoeff_abs_odd (j : ℕ) :
    chebyshevCoeff (fun x : ℝ => |x|) (2 * j + 1) = 0 := by
  rw [chebyshevCoeff_abs_eq_half_integral]
  simp [pow_add, pow_mul]

/-- Product-to-sum integrates the positive even absolute-value frequency explicitly.
Source: Trefethen, ATAP, Exercise 3.6; helper for `chebyshev-series-abs-sign`. -/
theorem integral_cos_mul_cos_even_half_pi {j : ℕ} (hj : 0 < j) :
    (∫ θ in 0..Real.pi / 2, Real.cos θ * Real.cos ((2 * j : ℕ) * θ)) =
      -((-1 : ℝ) ^ j) / (4 * (j : ℝ) ^ 2 - 1) := by
  have hpos : (1 : ℝ) + 2 * j ≠ 0 := by positivity
  have hneg : (1 : ℝ) - 2 * j ≠ 0 := by
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hproduct : ∀ θ : ℝ, Real.cos θ * Real.cos ((2 * j : ℕ) * θ) =
      (Real.cos ((1 + 2 * j) * θ) + Real.cos ((1 - 2 * j) * θ)) / 2 := by
    intro θ
    push_cast
    rw [show (1 + 2 * (j : ℝ)) * θ = θ + 2 * (j : ℝ) * θ by ring,
      show (1 - 2 * (j : ℝ)) * θ = θ - 2 * (j : ℝ) * θ by ring,
      Real.cos_add, Real.cos_sub]
    ring
  simp_rw [hproduct]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_mul_half_pi _ hpos, integral_cos_mul_half_pi _ hneg]
  have hsinplus : Real.sin ((1 + 2 * (j : ℝ)) * (Real.pi / 2)) = (-1 : ℝ) ^ j := by
    rw [show (1 + 2 * (j : ℝ)) * (Real.pi / 2) = (j : ℝ) * Real.pi + Real.pi / 2 by ring]
    simp [Real.sin_add, Real.cos_nat_mul_pi]
  have hsinminus : Real.sin ((1 - 2 * (j : ℝ)) * (Real.pi / 2)) = (-1 : ℝ) ^ j := by
    rw [show (1 - 2 * (j : ℝ)) * (Real.pi / 2) = Real.pi / 2 - (j : ℝ) * Real.pi by ring]
    simp [Real.sin_sub, Real.cos_nat_mul_pi]
  rw [hsinplus, hsinminus]
  rw [show 4 * (j : ℝ) ^ 2 - 1 = -((1 + 2 * (j : ℝ)) * (1 - 2 * (j : ℝ))) by ring]
  field_simp [hpos, hneg]
  ring

/-- The positive even Chebyshev coefficients of absolute value are the exact classical fractions.
Source: Trefethen, ATAP, Exercise 3.6.
atlas: chebyshev-series-abs-sign (partial) -/
theorem chebyshevCoeff_abs_even {j : ℕ} (hj : 0 < j) :
    chebyshevCoeff (fun x : ℝ => |x|) (2 * j) =
      4 / Real.pi * (-1 : ℝ) ^ (j + 1) / (4 * (j : ℝ) ^ 2 - 1) := by
  rw [chebyshevCoeff_abs_eq_half_integral,
    if_neg (show 2 * j ≠ 0 by omega), integral_cos_mul_cos_even_half_pi hj]
  simp [pow_mul, pow_succ]
  ring

/-- Absolute value is one-Lipschitz, including its nondifferentiable origin.
Source: reverse triangle inequality; helper for `chebyshev-series-abs-sign`. -/
theorem lipschitzWith_abs : LipschitzWith 1 (fun x : ℝ => |x|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y

/-- The genuine absolute-value coefficients are absolutely summable.
Source: Trefethen, ATAP, Exercise 3.6; helper for `chebyshev-series-abs-sign`. -/
theorem summable_abs_chebyshevCoeff_abs :
    Summable (fun k => |chebyshevCoeff (fun x : ℝ => |x|) k|) :=
  summable_abs_chebyshevCoeff_of_lipschitzOnWith lipschitzWith_abs.lipschitzOnWith

/-- Absolute value has its genuine absolute Chebyshev expansion.
Source: Trefethen, ATAP, Exercise 3.6.
atlas: chebyshev-series-abs-sign (partial) -/
theorem hasSum_chebyshevCoeff_abs_mul_eval_T {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k => chebyshevCoeff (fun x : ℝ => |x|) k * (T ℝ (k : ℤ)).eval x) |x| :=
  hasSum_chebyshevCoeff_mul_eval_T (by fun_prop) summable_abs_chebyshevCoeff_abs hx

/-- The absolute-value Chebyshev expansion converges uniformly on the entire closed interval.
Source: Trefethen, ATAP, Exercise 3.6.
atlas: chebyshev-series-abs-sign (partial) -/
theorem tendstoUniformlyOn_chebyshevTrunc_abs :
    TendstoUniformlyOn (fun n x => (chebyshevTrunc (fun x : ℝ => |x|) n).eval x)
      (fun x : ℝ => |x|) atTop (Icc (-1 : ℝ) 1) :=
  tendstoUniformlyOn_chebyshevTrunc (by fun_prop) summable_abs_chebyshevCoeff_abs

/-- Absolute values of the positive even coefficients are exact positive fractions.
Source: Trefethen, ATAP, Exercise 3.6; helper for `chebyshev-series-abs-sign`. -/
theorem abs_chebyshevCoeff_abs_even {j : ℕ} (hj : 0 < j) :
    |chebyshevCoeff (fun x : ℝ => |x|) (2 * j)| =
      4 / Real.pi / (4 * (j : ℝ) ^ 2 - 1) := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hden : 0 < 4 * (j : ℝ) ^ 2 - 1 := by nlinarith
  rw [chebyshevCoeff_abs_even hj, abs_div, abs_mul,
    abs_of_pos (show (0 : ℝ) < 4 / Real.pi by positivity), abs_pow,
    abs_of_pos hden]
  norm_num

/-- Every positive even coefficient norm is a two-term telescope.
Source: Trefethen, ATAP, Exercise 3.6; helper for `chebyshev-series-abs-sign`. -/
theorem abs_chebyshevCoeff_abs_even_eq_sub (j : ℕ) :
    |chebyshevCoeff (fun x : ℝ => |x|) (2 * (j + 1))| =
      2 / Real.pi * (1 / (2 * (j : ℝ) + 1) - 1 / (2 * (j : ℝ) + 3)) := by
  rw [abs_chebyshevCoeff_abs_even (by omega)]
  have hfac : 4 * ((j + 1 : ℕ) : ℝ) ^ 2 - 1 = (2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 3) := by
    push_cast
    ring
  rw [hfac]
  field_simp
  ring

/-- Summing the positive even coefficient telescope gives the exact omitted tail.
Source: Trefethen, ATAP, Exercise 3.6; operator rederivations `polyseries:abstail`.
atlas: chebyshev-series-abs-sign (partial) -/
theorem hasSum_abs_chebyshevCoeff_abs_even_tail (m : ℕ) :
    HasSum (fun j => |chebyshevCoeff (fun x : ℝ => |x|) (2 * (j + m + 1))|)
      (2 / (Real.pi * (2 * m + 1))) := by
  let b : ℕ → ℝ := fun j => 1 / (2 * ((j + m : ℕ) : ℝ) + 1)
  have hs : Summable (fun j => |chebyshevCoeff (fun x : ℝ => |x|) (2 * (j + m + 1))|) :=
    summable_abs_chebyshevCoeff_abs.comp_injective (by
      intro a c h
      change 2 * (a + m + 1) = 2 * (c + m + 1) at h
      omega)
  have hn : Summable (fun j => ‖|chebyshevCoeff (fun x : ℝ => |x|) (2 * (j + m + 1))|‖) := by
    simpa only [Real.norm_of_nonneg (abs_nonneg _)] using hs
  have hterm : ∀ j, |chebyshevCoeff (fun x : ℝ => |x|) (2 * (j + m + 1))| =
      2 / Real.pi * (b j - b (j + 1)) := by
    intro j
    rw [abs_chebyshevCoeff_abs_even_eq_sub]
    dsimp only [b]
    push_cast
    congr 2
    ring
  apply (hasSum_iff_tendsto_nat_of_summable_norm hn).mpr
  have hzero : Tendsto b atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun j => by dsimp [b]; positivity))
      _ (show Tendsto (fun j : ℕ => (j : ℝ)⁻¹) atTop (𝓝 0) from tendsto_inv_atTop_nhds_zero_nat)
    filter_upwards [eventually_ge_atTop 1] with j hj
    dsimp only [b]
    have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hden : (j : ℝ) ≤ 2 * ((j + m : ℕ) : ℝ) + 1 := by push_cast; nlinarith
    simpa only [one_div] using one_div_le_one_div_of_le hjR hden
  have hsum : (fun N : ℕ => ∑ j ∈ range N,
      |chebyshevCoeff (fun x : ℝ => |x|) (2 * (j + m + 1))|) =
      fun N => 2 / Real.pi * (b 0 - b N) := by
    funext N
    simp_rw [hterm]
    rw [← mul_sum, sum_range_sub']
  rw [hsum]
  have ht := ((tendsto_const_nhds (x := b 0)).sub hzero).const_mul (2 / Real.pi)
  have hvalue : 2 / Real.pi * (b 0 - 0) = 2 / (Real.pi * (2 * m + 1)) := by
    dsimp only [b]
    push_cast
    field_simp
    ring
  rw [hvalue] at ht
  exact ht

/-- The complete coefficient tail after degree `2m` is exactly `2/(π(2m+1))`.
Source: Trefethen, ATAP, Exercise 3.6; odd coefficients vanish.
atlas: chebyshev-series-abs-sign (partial) -/
theorem tsum_abs_chebyshevCoeff_abs_tail (m : ℕ) :
    (∑' j, |chebyshevCoeff (fun x : ℝ => |x|) (j + (2 * m + 1))|) =
      2 / (Real.pi * (2 * m + 1)) := by
  let u : ℕ → ℝ := fun j => |chebyshevCoeff (fun x : ℝ => |x|) (j + (2 * m + 1))|
  have hs : Summable u := (summable_nat_add_iff (2 * m + 1)).mpr summable_abs_chebyshevCoeff_abs
  have he : Summable (fun j => u (2 * j)) := hs.comp_injective (by
    intro a b h
    change 2 * a = 2 * b at h
    omega)
  have ho : Summable (fun j => u (2 * j + 1)) := hs.comp_injective (by
    intro a b h
    change 2 * a + 1 = 2 * b + 1 at h
    omega)
  have hzero : ∀ j, u (2 * j) = 0 := by
    intro j
    dsimp only [u]
    rw [show 2 * j + (2 * m + 1) = 2 * (j + m) + 1 by omega, chebyshevCoeff_abs_odd, abs_zero]
  have hodd : ∀ j, u (2 * j + 1) = |chebyshevCoeff (fun x : ℝ => |x|) (2 * (j + m + 1))| := by
    intro j
    dsimp only [u]
    rw [show 2 * j + 1 + (2 * m + 1) = 2 * (j + m + 1) by omega]
  have h := tsum_even_add_odd he ho
  simp_rw [hzero, hodd] at h
  rw [tsum_zero, zero_add, (hasSum_abs_chebyshevCoeff_abs_even_tail m).tsum_eq] at h
  exact h.symm

/-- The degree-`2m` Chebyshev truncation approximates absolute value with its exact tail constant.
Source: Trefethen, ATAP, Exercise 3.6.
atlas: chebyshev-series-abs-sign (partial) -/
theorem abs_abs_sub_eval_chebyshevTrunc_le (m : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(|x|) - (chebyshevTrunc (fun x : ℝ => |x|) (2 * m)).eval x| ≤
      2 / (Real.pi * (2 * m + 1)) := by
  have h := abs_sub_eval_chebyshevTrunc_le_tsum (f := fun x : ℝ => |x|)
    (by fun_prop) summable_abs_chebyshevCoeff_abs (2 * m) hx
  simpa only [tsum_abs_chebyshevCoeff_abs_tail] using h

end NLAlib
