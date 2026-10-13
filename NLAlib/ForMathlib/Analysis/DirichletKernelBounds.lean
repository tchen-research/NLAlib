import NLAlib.ForMathlib.Analysis.FejerKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Real Dirichlet kernels and their logarithmic integral bound

Finite trigonometric telescopes identify the circle kernel on real angles.
-/

noncomputable section

open Real Finset MeasureTheory
open scoped NLAlib.TwoPi

namespace NLAlib

/-- The circle Dirichlet kernel is the usual finite cosine sum on real angles.
Source: finite Fourier characters; helper for `chebyshev-projection-lebesgue-constant`. -/
theorem dirichletCircleKernel_coe (n : ℕ) (θ : ℝ) :
    dirichletCircleKernel n (θ : AddCircle (2 * π)) =
      1 + 2 * ∑ k ∈ range n, cos ((k + 1 : ℕ) * θ) := by
  simp only [dirichletCircleKernel, re_fourier_nat_coe_eq_cos]

/-- Multiplication by the half-angle sine removes all singularities from the
closed form of the Dirichlet kernel.
Source: finite sine telescope; focused rederivations `thm:projection`. -/
theorem sin_half_mul_dirichletCircleKernel_coe (n : ℕ) (θ : ℝ) :
    sin (θ / 2) * dirichletCircleKernel n (θ : AddCircle (2 * π)) =
      sin (((n : ℝ) + 1 / 2) * θ) := by
  rw [dirichletCircleKernel_coe, mul_add, ← mul_assoc, mul_sum]
  have hterm : ∀ k : ℕ,
      sin (θ / 2) * (2 * cos ((k + 1 : ℕ) * θ)) =
        sin (((k + 1 : ℕ) + (1 / 2 : ℝ)) * θ) -
          sin (((k : ℝ) + 1 / 2) * θ) := by
    intro k
    have hp : (((k + 1 : ℕ) : ℝ) + 1 / 2) * θ =
        ((k + 1 : ℕ) : ℝ) * θ + θ / 2 := by ring
    have hm : ((k : ℝ) + 1 / 2) * θ =
        ((k + 1 : ℕ) : ℝ) * θ - θ / 2 := by push_cast; ring
    rw [hp, hm, sin_add, sin_sub]
    ring
  simp_rw [mul_assoc, hterm]
  rw [sum_range_sub (fun k : ℕ => sin (((k : ℝ) + 1 / 2) * θ))]
  simp only [Nat.cast_zero, zero_add, mul_one]
  rw [show (1 / 2 : ℝ) * θ = θ / 2 by ring]
  ring

/-- The classical sine quotient for the Dirichlet kernel away from removable
singularities.
Source: finite sine telescope; focused rederivations `thm:projection`. -/
theorem dirichletCircleKernel_coe_eq_sin_div (n : ℕ) (θ : ℝ)
    (hθ : sin (θ / 2) ≠ 0) :
    dirichletCircleKernel n (θ : AddCircle (2 * π)) =
      sin (((n : ℝ) + 1 / 2) * θ) / sin (θ / 2) := by
  apply (eq_div_iff hθ).mpr
  rw [mul_comm]
  exact sin_half_mul_dirichletCircleKernel_coe n θ

/-- The Dirichlet kernel has its finite value `2n+1` at the origin.
Source: finite Fourier characters; focused rederivations `thm:projection`. -/
@[simp] theorem dirichletCircleKernel_zero (n : ℕ) :
    dirichletCircleKernel n 0 = 2 * (n : ℝ) + 1 := by
  have h := dirichletCircleKernel_coe n 0
  simpa only [AddCircle.coe_zero, mul_zero, cos_zero, sum_const, card_range,
    nsmul_eq_mul, mul_one, add_comm] using h

/-- A reciprocal sine bound with the correct singular coefficient at zero.
Source: `sin u ≥ u-u³/6`; focused rederivations `thm:projection`. -/
theorem one_div_sin_half_le (t : ℝ) (ht : 0 < t) (htπ : t ≤ π) :
    1 / sin (t / 2) ≤ 2 / t + t / 4 := by
  have hu : 0 < t / 2 := by positivity
  have hu2 : t / 2 < 2 := by linarith [Real.pi_lt_four]
  have hs : 0 < sin (t / 2) := sin_pos_of_mem_Ioo ⟨hu, by linarith [pi_pos]⟩
  have hlo := sin_ge_sub_cube hu.le
  have hfac : 0 ≤ 1 / (t / 2) + (t / 2) / 2 := by positivity
  have hsq : 0 ≤ (t / 2) ^ 2 * (4 - (t / 2) ^ 2) := by
    apply mul_nonneg (sq_nonneg _)
    nlinarith
  apply (div_le_iff₀ hs).mpr
  have hid : (2 / t + t / 4) * (t / 2 - (t / 2) ^ 3 / 6) =
      1 + (t / 2) ^ 2 * (4 - (t / 2) ^ 2) / 12 := by
    field_simp
    ring
  have hmul := mul_le_mul_of_nonneg_left hlo hfac
  have hfactor : 1 / (t / 2) + (t / 2) / 2 = 2 / t + t / 4 := by ring
  rw [hfactor, hid] at hmul
  nlinarith

/-- The pointwise Dirichlet kernel bound separates an integrable sinc term
from a harmless linear remainder.
Source: reciprocal sine estimate; focused rederivations `thm:projection`. -/
theorem abs_dirichletCircleKernel_coe_le_sinc (n : ℕ) (t : ℝ)
    (ht : 0 < t) (htπ : t ≤ π) :
    |dirichletCircleKernel n (t : AddCircle (2 * π))| ≤
      2 * ((n : ℝ) + 1 / 2) * |sinc (((n : ℝ) + 1 / 2) * t)| + t / 4 := by
  have hs : 0 < sin (t / 2) :=
    sin_pos_of_mem_Ioo ⟨by positivity, by linarith [pi_pos]⟩
  have hM : 0 < (n : ℝ) + 1 / 2 := by positivity
  have hMt : 0 < ((n : ℝ) + 1 / 2) * t := mul_pos hM ht
  rw [dirichletCircleKernel_coe_eq_sin_div n t hs.ne', abs_div, abs_of_pos hs]
  calc
    |sin (((n : ℝ) + 1 / 2) * t)| / sin (t / 2)
        = |sin (((n : ℝ) + 1 / 2) * t)| * (1 / sin (t / 2)) := by ring
    _ ≤ |sin (((n : ℝ) + 1 / 2) * t)| * (2 / t + t / 4) :=
      mul_le_mul_of_nonneg_left (one_div_sin_half_le t ht htπ) (abs_nonneg _)
    _ ≤ 2 * ((n : ℝ) + 1 / 2) * |sinc (((n : ℝ) + 1 / 2) * t)| + t / 4 := by
      rw [sinc_of_ne_zero hMt.ne', abs_div, abs_of_pos hMt]
      have hsin := abs_sin_le_one (((n : ℝ) + 1 / 2) * t)
      have hid : 2 * ((n : ℝ) + 1 / 2) *
          (|sin (((n : ℝ) + 1 / 2) * t)| / (((n : ℝ) + 1 / 2) * t)) =
          |sin (((n : ℝ) + 1 / 2) * t)| * (2 / t) := by field_simp
      rw [hid, mul_add]
      nlinarith

/-- The absolute sine has integral two over every complete half-period.
Source: elementary sine integration; focused rederivations `thm:projection`. -/
theorem integral_abs_sin_nat_pi (j : ℕ) :
    (∫ x in (j : ℝ) * π..(j + 1 : ℕ) * π, |sin x|) = 2 := by
  have hshift : ∀ x : ℝ, |sin (x + (j : ℝ) * π)| = |sin x| := by
    intro x
    rw [sin_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have h := intervalIntegral.integral_comp_add_right (fun x : ℝ => |sin x|)
    ((j : ℝ) * π) (a := 0) (b := π)
  rw [intervalIntegral.integral_congr (fun x _ => hshift x)] at h
  have hend : π + (j : ℝ) * π = (j + 1 : ℕ) * π := by push_cast; ring
  rw [zero_add, hend] at h
  rw [← h]
  calc
    (∫ x in 0..π, |sin x|) = ∫ x in 0..π, sin x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le pi_pos.le] at hx
      exact abs_of_nonneg (sin_nonneg_of_mem_Icc hx)
    _ = 2 := by rw [integral_sin]; norm_num

/-- The sinc integral over the initial half-period is at most `π`.
Source: `|sinc| ≤ 1`; focused rederivations `thm:projection`. -/
theorem integral_abs_sinc_zero_pi_le : (∫ x in 0..π, |sinc x|) ≤ π := by
  calc
    _ ≤ ∫ x in (0 : ℝ)..π, (1 : ℝ) :=
      intervalIntegral.integral_mono_on pi_pos.le
        (continuous_sinc.abs.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
        (fun x _ => abs_sinc_le_one x)
    _ = π := by simp

/-- Later complete half-periods of sinc have a harmonic upper bound.
Source: comparison with the left endpoint reciprocal;
focused rederivations `thm:projection`. -/
theorem integral_abs_sinc_nat_pi_le (j : ℕ) (hj : 0 < j) :
    (∫ x in (j : ℝ) * π..(j + 1 : ℕ) * π, |sinc x|) ≤ 2 / ((j : ℝ) * π) := by
  have hlow : 0 < (j : ℝ) * π := mul_pos (by exact_mod_cast hj) pi_pos
  have hab : (j : ℝ) * π ≤ (j + 1 : ℕ) * π := by push_cast; nlinarith [pi_pos]
  calc
    _ ≤ ∫ x in (j : ℝ) * π..(j + 1 : ℕ) * π, |sin x| / ((j : ℝ) * π) := by
      apply intervalIntegral.integral_mono_on hab
        (continuous_sinc.abs.intervalIntegrable _ _)
        ((continuous_sin.abs.div_const _).intervalIntegrable _ _)
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hlow hx.1
      rw [sinc_of_ne_zero hx0.ne', abs_div, abs_of_pos hx0]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hlow hx.1
    _ = 2 / ((j : ℝ) * π) := by
      rw [intervalIntegral.integral_div, integral_abs_sin_nat_pi]

/-- The sinc integral through any number of complete half-periods has the
sharp harmonic coefficient `2/π`.
Source: complete-period decomposition; focused rederivations `thm:projection`. -/
theorem integral_abs_sinc_nat_pi_le_harmonic (n : ℕ) :
    (∫ x in 0..(n + 1 : ℕ) * π, |sinc x|) ≤ π + (2 / π) * (harmonic n : ℝ) := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume)
    (a := fun j : ℕ => (j : ℝ) * π) (n := n + 1)
    (f := fun x : ℝ => |sinc x|)
    (fun _ _ => continuous_sinc.abs.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_mul] at hsplit
  rw [← hsplit, sum_range_succ']
  calc
    _ ≤ (∑ j ∈ range n, 2 / (((j + 1 : ℕ) : ℝ) * π)) + π := by
      apply add_le_add
      · apply sum_le_sum
        intro j _
        exact integral_abs_sinc_nat_pi_le (j + 1) (by omega)
      · simpa using integral_abs_sinc_zero_pi_le
    _ = π + (2 / π) * (harmonic n : ℝ) := by
      rw [harmonic, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
      rw [mul_sum]
      have hterm : ∀ j : ℕ, 2 / (((j + 1 : ℕ) : ℝ) * π) =
          (2 / π) * (((j + 1 : ℕ) : ℝ)⁻¹) := by intro j; ring
      simp_rw [hterm]
      ring

/-- The positive-angle Dirichlet integral has the sharp harmonic coefficient.
Source: reciprocal sine and complete-period estimates;
focused rederivations `thm:projection`. -/
theorem integral_abs_dirichletCircleKernel_zero_pi_le_harmonic (n : ℕ) :
    (∫ t in 0..π, |dirichletCircleKernel n (t : AddCircle (2 * π))|) ≤
      2 * (π + (2 / π) * (harmonic n : ℝ)) + π ^ 2 / 8 := by
  let M : ℝ := (n : ℝ) + 1 / 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : Continuous (fun t : ℝ => |dirichletCircleKernel n (t : AddCircle (2 * π))|) := by
    exact (continuous_dirichletCircleKernel n |>.comp (AddCircle.continuous_mk' (2 * π))).abs
  have hB : Continuous (fun t : ℝ => 2 * M * |sinc (M * t)| + t / 4) := by
    fun_prop
  have hbound : (∫ t in 0..π, |dirichletCircleKernel n (t : AddCircle (2 * π))|) ≤
      ∫ t in 0..π, 2 * M * |sinc (M * t)| + t / 4 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo pi_pos.le
      (hD.intervalIntegrable _ _) (hB.intervalIntegrable _ _)
    intro t ht
    exact abs_dirichletCircleKernel_coe_le_sinc n t ht.1 ht.2.le
  have hchange : M * (∫ t in 0..π, |sinc (M * t)|) = ∫ t in 0..M * π, |sinc t| := by
    simpa only [smul_eq_mul, mul_zero] using
      intervalIntegral.smul_integral_comp_mul_left (fun t : ℝ => |sinc t|) M
        (a := 0) (b := π)
  have hsinc : (∫ t in 0..M * π, |sinc t|) ≤ π + (2 / π) * (harmonic n : ℝ) := by
    apply le_trans _ (integral_abs_sinc_nat_pi_le_harmonic n)
    apply intervalIntegral.integral_mono_interval le_rfl (mul_nonneg hM.le pi_pos.le)
    · dsimp [M]
      push_cast
      nlinarith [pi_pos]
    · exact ae_of_all _ (fun _ => abs_nonneg _)
    · exact continuous_sinc.abs.intervalIntegrable _ _
  have hint : (∫ t in 0..π, 2 * M * |sinc (M * t)| + t / 4) =
      2 * (∫ t in 0..M * π, |sinc t|) + π ^ 2 / 8 := by
    rw [intervalIntegral.integral_add
      ((show Continuous (fun t : ℝ => 2 * M * |sinc (M * t)|) by fun_prop).intervalIntegrable _ _)
      ((show Continuous (fun t : ℝ => t / 4) by fun_prop).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div, integral_id]
    rw [show 2 * M * (∫ t in 0..π, |sinc (M * t)|) =
      2 * (M * (∫ t in 0..π, |sinc (M * t)|)) by ring, hchange]
    ring
  rw [hint] at hbound
  linarith

/-- The normalized absolute Dirichlet kernel is at most
`3 + (4/π²) log(n+1)`.
Source: complete-period harmonic estimates;
focused rederivations `thm:projection`. -/
theorem integral_abs_dirichletCircleKernel_zero_pi_div_pi_le_log (n : ℕ) :
    (1 / π) * (∫ t in 0..π, |dirichletCircleKernel n (t : AddCircle (2 * π))|) ≤
      3 + (4 / π ^ 2) * log (n + 1 : ℕ) := by
  have hH : (harmonic n : ℝ) ≤ 1 + log (n + 1 : ℕ) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      apply (harmonic_le_one_add_log n).trans
      gcongr
      linarith
  have hD := mul_le_mul_of_nonneg_left
    (integral_abs_dirichletCircleKernel_zero_pi_le_harmonic n) (one_div_nonneg.mpr pi_pos.le)
  have hH' := mul_le_mul_of_nonneg_left hH (show 0 ≤ 4 / π ^ 2 by positivity)
  have hconst : π / 8 + 4 / π ^ 2 < 1 := by
    have hpi := Real.pi_lt_four
    have hpi3 := Real.pi_gt_three
    have hdiv : 4 / π ^ 2 < 4 / 9 := by
      apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
      nlinarith
    linarith
  have hid : (1 / π) * (2 * (π + (2 / π) * (harmonic n : ℝ)) + π ^ 2 / 8) =
      2 + (4 / π ^ 2) * (harmonic n : ℝ) + π / 8 := by
    field_simp
    ring
  rw [hid] at hD
  linarith

/-- The normalized Haar integral of an even Dirichlet kernel is its positive
half-period integral divided by `π`.
Source: Haar normalization and reflection; focused rederivations `thm:projection`. -/
theorem integral_abs_dirichletCircleKernel_eq_half_period (n : ℕ) :
    (∫ t : AddCircle (2 * π), |dirichletCircleKernel n t| ∂AddCircle.haarAddCircle) =
      (1 / π) * ∫ t in 0..π, |dirichletCircleKernel n (t : AddCircle (2 * π))| := by
  let u : ℝ → ℝ := fun t => |dirichletCircleKernel n (t : AddCircle (2 * π))|
  have hu : Continuous u :=
    (continuous_dirichletCircleKernel n |>.comp (AddCircle.continuous_mk' (2 * π))).abs
  have heven : ∀ t : ℝ, u (-t) = u t := by
    intro t
    simp only [u, dirichletCircleKernel_coe, mul_neg, cos_neg]
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * π) (-π)]
  simp only [smul_eq_mul]
  have hreflect : (∫ t in -π..0, u t) = ∫ t in 0..π, u t := by
    have h := intervalIntegral.integral_comp_neg (f := u) (a := 0) (b := π)
    simp only [neg_zero] at h
    simpa only [heven] using h.symm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hu.intervalIntegrable (-π) 0) (hu.intervalIntegrable 0 π)
  rw [hreflect] at hsplit
  rw [show -π + 2 * π = π by ring]
  change (2 * π)⁻¹ * (∫ t in -π..π, u t) = (1 / π) * (∫ t in 0..π, u t)
  rw [← hsplit]
  ring

/-- The absolute Dirichlet kernel has the sharp logarithmic Haar upper bound.
Source: complete-period harmonic estimates; focused rederivations `thm:projection`.
Helper for `chebyshev-projection-lebesgue-constant`. -/
theorem integral_abs_dirichletCircleKernel_le_log (n : ℕ) :
    (∫ t : AddCircle (2 * π), |dirichletCircleKernel n t| ∂AddCircle.haarAddCircle) ≤
      3 + (4 / π ^ 2) * log (n + 1 : ℕ) := by
  rw [integral_abs_dirichletCircleKernel_eq_half_period]
  exact integral_abs_dirichletCircleKernel_zero_pi_div_pi_le_log n

/-- The reciprocal half-angle sine has the matching singular lower coefficient.
Source: `sin u ≤ u`; focused rederivations `thm:projection`. -/
theorem two_div_le_one_div_sin_half (t : ℝ) (ht : 0 < t) (htπ : t ≤ π) :
    2 / t ≤ 1 / sin (t / 2) := by
  have hs : 0 < sin (t / 2) := sin_pos_of_mem_Ioo ⟨by positivity, by linarith [pi_pos]⟩
  have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) hs
    (sin_le (by positivity : 0 ≤ t / 2))
  have heq : (1 : ℝ) / (t / 2) = 2 / t := by ring
  rw [heq] at h
  exact h

/-- The absolute Dirichlet kernel dominates its sinc singular part.
Source: reciprocal sine lower bound; focused rederivations `thm:projection`. -/
theorem sinc_le_abs_dirichletCircleKernel_coe (n : ℕ) (t : ℝ)
    (ht : 0 < t) (htπ : t ≤ π) :
    2 * ((n : ℝ) + 1 / 2) * |sinc (((n : ℝ) + 1 / 2) * t)| ≤
      |dirichletCircleKernel n (t : AddCircle (2 * π))| := by
  have hs : 0 < sin (t / 2) :=
    sin_pos_of_mem_Ioo ⟨by positivity, by linarith [pi_pos]⟩
  have hMt : 0 < ((n : ℝ) + 1 / 2) * t := by positivity
  rw [dirichletCircleKernel_coe_eq_sin_div n t hs.ne', abs_div, abs_of_pos hs,
    sinc_of_ne_zero hMt.ne', abs_div, abs_of_pos hMt]
  have h := mul_le_mul_of_nonneg_left (two_div_le_one_div_sin_half t ht htπ)
    (abs_nonneg (sin (((n : ℝ) + 1 / 2) * t)))
  have hid : 2 * ((n : ℝ) + 1 / 2) *
      (|sin (((n : ℝ) + 1 / 2) * t)| / (((n : ℝ) + 1 / 2) * t)) =
      |sin (((n : ℝ) + 1 / 2) * t)| * (2 / t) := by field_simp
  rw [hid, show |sin (((n : ℝ) + 1 / 2) * t)| / sin (t / 2) =
    |sin (((n : ℝ) + 1 / 2) * t)| * (1 / sin (t / 2)) by ring]
  exact h

/-- Each complete half-period gives a harmonic lower bound for the sinc integral.
Source: comparison with the right endpoint reciprocal;
focused rederivations `thm:projection`. -/
theorem two_div_nat_pi_le_integral_abs_sinc (j : ℕ) :
    2 / ((j + 1 : ℕ) * π) ≤ ∫ x in (j : ℝ) * π..(j + 1 : ℕ) * π, |sinc x| := by
  have hhigh : 0 < ((j + 1 : ℕ) : ℝ) * π := by positivity
  have hab : (j : ℝ) * π ≤ (j + 1 : ℕ) * π := by push_cast; nlinarith [pi_pos]
  calc
    _ = ∫ x in (j : ℝ) * π..(j + 1 : ℕ) * π, |sin x| / ((j + 1 : ℕ) * π) := by
      rw [intervalIntegral.integral_div, integral_abs_sin_nat_pi]
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hab
        ((continuous_sin.abs.div_const _).intervalIntegrable _ _)
        (continuous_sinc.abs.intervalIntegrable _ _)
      intro x hx
      have hx0 : 0 < x := lt_of_le_of_lt (by positivity) hx.1
      rw [sinc_of_ne_zero hx0.ne', abs_div, abs_of_pos hx0]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hx0 hx.2.le

/-- Complete half-periods give the sharp harmonic lower coefficient for sinc.
Source: finite complete-period decomposition; focused rederivations `thm:projection`. -/
theorem harmonic_le_integral_abs_sinc_nat_pi (n : ℕ) :
    (2 / π) * (harmonic n : ℝ) ≤ ∫ x in 0..(n : ℝ) * π, |sinc x| := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := fun j : ℕ => (j : ℝ) * π) (n := n)
    (f := fun x : ℝ => |sinc x|)
    (fun _ _ => continuous_sinc.abs.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_mul] at hsplit
  rw [← hsplit, harmonic, Rat.cast_sum, mul_sum]
  apply sum_le_sum
  intro j _
  simp only [Rat.cast_inv, Rat.cast_natCast]
  have hterm : (2 / π) * (((j + 1 : ℕ) : ℝ)⁻¹) =
      2 / (((j + 1 : ℕ) : ℝ) * π) := by ring
  rw [hterm]
  exact two_div_nat_pi_le_integral_abs_sinc j

/-- The normalized absolute Dirichlet integral has the matching harmonic lower
bound `4H_n/π²`, proving sharpness of the logarithmic coefficient.
Source: reciprocal sine and complete-period lower estimates;
focused rederivations `thm:projection`. -/
theorem harmonic_le_integral_abs_dirichletCircleKernel (n : ℕ) :
    (4 / π ^ 2) * (harmonic n : ℝ) ≤
      ∫ t : AddCircle (2 * π), |dirichletCircleKernel n t| ∂AddCircle.haarAddCircle := by
  let M : ℝ := (n : ℝ) + 1 / 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hD : Continuous (fun t : ℝ => |dirichletCircleKernel n (t : AddCircle (2 * π))|) :=
    (continuous_dirichletCircleKernel n |>.comp (AddCircle.continuous_mk' (2 * π))).abs
  have hchange : M * (∫ t in 0..π, |sinc (M * t)|) = ∫ t in 0..M * π, |sinc t| := by
    simpa only [smul_eq_mul, mul_zero] using
      intervalIntegral.smul_integral_comp_mul_left (fun t : ℝ => |sinc t|) M
        (a := 0) (b := π)
  have hpoint : (∫ t in 0..π, 2 * M * |sinc (M * t)|) ≤
      ∫ t in 0..π, |dirichletCircleKernel n (t : AddCircle (2 * π))| := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo pi_pos.le
      ((show Continuous (fun t : ℝ => 2 * M * |sinc (M * t)|) by fun_prop).intervalIntegrable _ _)
      (hD.intervalIntegrable _ _)
    intro t ht
    exact sinc_le_abs_dirichletCircleKernel_coe n t ht.1 ht.2.le
  rw [intervalIntegral.integral_const_mul, show 2 * M * (∫ t in 0..π, |sinc (M * t)|) =
    2 * (M * (∫ t in 0..π, |sinc (M * t)|)) by ring, hchange] at hpoint
  have hsinc : (∫ t in 0..(n : ℝ) * π, |sinc t|) ≤ ∫ t in 0..M * π, |sinc t| := by
    apply intervalIntegral.integral_mono_interval le_rfl (by positivity)
    · dsimp [M]
      nlinarith [pi_pos]
    · exact ae_of_all _ (fun _ => abs_nonneg _)
    · exact continuous_sinc.abs.intervalIntegrable _ _
  have hH := harmonic_le_integral_abs_sinc_nat_pi n
  have htotal : (4 / π) * (harmonic n : ℝ) ≤
      ∫ t in 0..π, |dirichletCircleKernel n (t : AddCircle (2 * π))| := by
    have heq : (4 / π) * (harmonic n : ℝ) = 2 * ((2 / π) * (harmonic n : ℝ)) := by ring
    rw [heq]
    linarith
  rw [integral_abs_dirichletCircleKernel_eq_half_period]
  have h := mul_le_mul_of_nonneg_left htotal (show 0 ≤ 1 / π by positivity)
  have hid : (4 / π ^ 2) * (harmonic n : ℝ) =
      (1 / π) * ((4 / π) * (harmonic n : ℝ)) := by ring
  rw [hid]
  exact h

end NLAlib
