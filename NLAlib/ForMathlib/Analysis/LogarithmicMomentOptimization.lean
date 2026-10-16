import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Logarithmic optimization of even moment bounds

An integer moment chosen by a ceiling gives a factor two leading variance
term and a square-root logarithmic correction. Keeping the exact `p - 1`
in the moment hypothesis yields correction constant four.
-/

noncomputable section
open Filter
open scoped Topology

namespace Real

/-- A positive dimension's reciprocal even powers tend to one. -/
theorem tendsto_const_rpow_inv_two_nat {d : ℝ} (hd : 0 < d) :
    Tendsto (fun p : ℕ => d ^ (1 / (2 * (p : ℝ)))) atTop (𝓝 1) := by
  have hden : Tendsto (fun p : ℕ => 2 * (p : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
  have hexp : Tendsto (fun p : ℕ => 1 / (2 * (p : ℝ))) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hden
  simpa only [Real.rpow_zero, Function.comp_def] using
    (Real.continuousAt_const_rpow hd.ne').tendsto.comp hexp

/-- The zero correction-scale endpoint of an even-moment estimate keeps
the exact factor two leading constant. -/
theorem le_two_mul_of_even_moments_zero {E σ d : ℝ} (hd : 0 < d)
    (hM : ∀ p : ℕ, 1 ≤ p → E ≤ 2 * d ^ (1 / (2 * (p : ℝ))) * σ) :
    E ≤ 2 * σ := by
  apply ge_of_tendsto (f := fun p : ℕ => 2 * d ^ (1 / (2 * (p : ℝ))) * σ)
    (by simpa only [mul_one] using
      (tendsto_const_nhds.mul (tendsto_const_rpow_inv_two_nat hd)).mul_const σ)
  filter_upwards [eventually_ge_atTop 1] with p hp
  exact hM p hp

/-- Ceiling optimization of the exact even moment bound. Keeping `p - 1`
yields correction constant four, which also implies the usual constant six.
This scalar theorem has no probabilistic assumptions. -/
theorem le_two_mul_add_four_mul_sqrt_log_of_even_moments
    {E σ κ d : ℝ} (hσ : 0 ≤ σ) (hκ : 0 ≤ κ) (hd : 1 < d)
    (hM : ∀ p : ℕ, 1 ≤ p → E ≤
      2 * d ^ (1 / (2 * (p : ℝ))) * Real.sqrt (σ ^ 2 + ((p - 1 : ℕ) : ℝ) * κ ^ 2)) :
    E ≤ 2 * σ + 4 * κ * Real.sqrt (Real.log d) := by
  by_cases hκ0 : κ = 0
  · subst κ
    have hh : E ≤ 2 * σ := le_two_mul_of_even_moments_zero (by linarith) (by
      intro p hp
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero,
        Real.sqrt_sq hσ] using hM p hp)
    simpa using hh
  have hκpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hκ0)
  let ℓ := Real.log d
  let L := Real.sqrt ℓ
  have hℓ : 0 < ℓ := Real.log_pos hd
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hLs : L ^ 2 = ℓ := Real.sq_sqrt hℓ.le
  let p : ℕ := ⌈ℓ + σ * L / κ⌉₊
  have hchoice : 0 < ℓ + σ * L / κ := by positivity
  have hp : 1 ≤ p := Nat.one_le_ceil_iff.mpr hchoice
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hlo : ℓ + σ * L / κ ≤ (p : ℝ) := Nat.le_ceil _
  have hhi : (p : ℝ) < ℓ + σ * L / κ + 1 := Nat.ceil_lt_add_one hchoice.le
  have hpminus : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp, Nat.cast_one]
  have hℓp : ℓ ≤ (p : ℝ) := by
    have hh : 0 ≤ σ * L / κ := by positivity
    linarith
  have hu₀ : 0 ≤ ℓ / (2 * (p : ℝ)) := by positivity
  have hu₁ : ℓ / (2 * (p : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (p : ℝ))).mpr
    linarith
  have hdim : d ^ (1 / (2 * (p : ℝ))) ≤ 1 + ℓ / (p : ℝ) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < d)]
    have he := Real.abs_exp_sub_one_le (show |ℓ / (2 * (p : ℝ))| ≤ 1 by
      simpa only [abs_of_nonneg hu₀] using hu₁)
    have hle := (le_abs_self (Real.exp (ℓ / (2 * (p : ℝ))) - 1)).trans he
    have heq : Real.log d * (1 / (2 * (p : ℝ))) = ℓ / (2 * (p : ℝ)) := by
      dsimp [ℓ]; ring
    rw [heq]
    rw [abs_of_nonneg hu₀] at hle
    have hratio : 2 * (ℓ / (2 * (p : ℝ))) = ℓ / (p : ℝ) := by field_simp
    linarith
  have hscaled : ((p - 1 : ℕ) : ℝ) * κ ^ 2 ≤ ℓ * κ ^ 2 + σ * κ * L := by
    have hh := mul_le_mul_of_nonneg_right (show (p : ℝ) - 1 ≤ ℓ + σ * L / κ by linarith)
      (sq_nonneg κ)
    have hc : (ℓ + σ * L / κ) * κ ^ 2 = ℓ * κ ^ 2 + σ * κ * L := by
      field_simp
    rw [hc, ← hpminus] at hh
    exact hh
  have hsum : (σ + κ * L) ^ 2 = σ ^ 2 + ℓ * κ ^ 2 + 2 * σ * κ * L := by
    rw [add_sq, mul_pow, hLs]
    ring
  have hroot : Real.sqrt (σ ^ 2 + ((p - 1 : ℕ) : ℝ) * κ ^ 2) ≤ σ + κ * L := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [hsum]
    nlinarith [mul_nonneg (mul_nonneg hσ hκ) hL]
  have hprod : ℓ / (p : ℝ) * (σ + κ * L) ≤ κ * L := by
    have hh := mul_le_mul_of_nonneg_right hlo (mul_nonneg hκ hL)
    have hc : (ℓ + σ * L / κ) * (κ * L) = ℓ * (σ + κ * L) := by
      field_simp
      nlinarith [congrArg (fun y : ℝ => σ * y) hLs]
    rw [hc] at hh
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hpR).mpr
    nlinarith
  calc
    E ≤ 2 * d ^ (1 / (2 * (p : ℝ))) *
        Real.sqrt (σ ^ 2 + ((p - 1 : ℕ) : ℝ) * κ ^ 2) := hM p hp
    _ ≤ 2 * (1 + ℓ / (p : ℝ)) * (σ + κ * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdim (by norm_num)) hroot
        (Real.sqrt_nonneg _) (by positivity)
    _ = 2 * σ + 2 * κ * L + 2 * (ℓ / (p : ℝ) * (σ + κ * L)) := by ring
    _ ≤ 2 * σ + 4 * κ * Real.sqrt (Real.log d) := by dsimp [L, ℓ] at *; linarith

end Real
