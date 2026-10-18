import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite Bessel inequality for the sine system

Direct orthogonality and the nonnegative integral of a finite residual square
give the sharp sine coefficient bound without an infinite-series derivative.
-/

noncomputable section

open Real MeasureTheory Finset Set

namespace Real

/-- Every nonzero integral cosine frequency has zero mean on `[0, π]`. -/
theorem integral_cos_int_mul_zero_pi {k : ℤ} (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..π, cos ((k : ℝ) * x)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left _ (by exact_mod_cast hk), integral_cos]
  simp [sin_int_mul_pi]

/-- The positive integral sine frequencies have squared norm `π/2` and are
pairwise orthogonal for ordinary Lebesgue integration on `[0, π]`. -/
theorem integral_sin_nat_mul_mul_sin_nat_mul {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    (∫ x in (0 : ℝ)..π, sin ((j : ℝ) * x) * sin ((k : ℝ) * x)) =
      if j = k then π / 2 else 0 := by
  have htrig (x : ℝ) : sin ((j : ℝ) * x) * sin ((k : ℝ) * x) =
      (cos (((j : ℝ) - k) * x) - cos (((j : ℝ) + k) * x)) / 2 := by
    rw [sub_mul, add_mul, cos_sub, cos_add]
    ring
  simp_rw [htrig]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hsum : (∫ x in (0 : ℝ)..π, cos (((j : ℝ) + k) * x)) = 0 := by
    exact_mod_cast integral_cos_int_mul_zero_pi (k := (j : ℤ) + k) (by omega)
  rw [hsum]
  by_cases heq : j = k
  · simp [heq]
  · have hdiff : (∫ x in (0 : ℝ)..π, cos (((j : ℝ) - k) * x)) = 0 := by
      exact_mod_cast integral_cos_int_mul_zero_pi (k := (j : ℤ) - k) (by omega)
    simp [heq, hdiff]

end Real

namespace NLAlib

/-- Finite sine Bessel inequality with the unnormalized coefficient integrals.
Only square integrability is used analytically; the proof expands a finite
residual square and never differentiates an infinite trigonometric series. -/
theorem sum_sq_le_two_div_pi_integral_sq_of_sine_coefficients
    {v : ℝ → ℝ} (hv : IntervalIntegrable v volume 0 π)
    (hv2 : IntervalIntegrable (fun x => v x ^ 2) volume 0 π)
    (s : Finset ℕ) (hs : ∀ j ∈ s, 0 < j) (c : ℕ → ℝ)
    (hc : ∀ j ∈ s, (∫ x in (0 : ℝ)..π, v x * sin ((j : ℝ) * x)) = π / 2 * c j) :
    (∑ j ∈ s, c j ^ 2) ≤ 2 / π * ∫ x in (0 : ℝ)..π, v x ^ 2 := by
  classical
  let q : ℝ → ℝ := fun x => ∑ j ∈ s, c j * sin ((j : ℝ) * x)
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hqs (j : ℕ) (hj : j ∈ s) :
      (∫ x in (0 : ℝ)..π, q x * sin ((j : ℝ) * x)) = π / 2 * c j := by
    simp only [q, sum_mul]
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
      Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
    have heq : ∀ k ∈ s, (∫ x in (0 : ℝ)..π,
        sin ((k : ℝ) * x) * sin ((j : ℝ) * x)) = if k = j then π / 2 else 0 :=
      fun k hk => integral_sin_nat_mul_mul_sin_nat_mul (hs k hk) (hs j hj)
    rw [sum_congr rfl (fun k hk => congrArg (fun a => c k * a) (heq k hk))]
    simp [hj, mul_ite, mul_comm]
  have hqq : (∫ x in (0 : ℝ)..π, q x ^ 2) = π / 2 * ∑ j ∈ s, c j ^ 2 := by
    have heq (x : ℝ) : q x ^ 2 = ∑ j ∈ s, c j * (q x * sin ((j : ℝ) * x)) := by
      calc
        q x ^ 2 = q x * (∑ j ∈ s, c j * sin ((j : ℝ) * x)) := by
          change q x ^ 2 = q x * q x
          ring
        _ = ∑ j ∈ s, q x * (c j * sin ((j : ℝ) * x)) := mul_sum ..
        _ = _ := sum_congr rfl (fun j _ => by ring)
    simp_rw [heq]
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
      Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [hqs j hj]
    ring
  have hvq : IntervalIntegrable (fun x => v x * q x) volume 0 π :=
    hv.mul_continuousOn hq.continuousOn
  have hvqeq : (∫ x in (0 : ℝ)..π, v x * q x) = π / 2 * ∑ j ∈ s, c j ^ 2 := by
    have heq (x : ℝ) : v x * q x = ∑ j ∈ s, c j * (v x * sin ((j : ℝ) * x)) := by
      dsimp [q]
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
      (hv.mul_continuousOn (by fun_prop)).const_mul (c j))]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [hc j hj]
    ring
  have hnonneg := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (a := (0 : ℝ)) (b := π) pi_pos.le (fun x => sq_nonneg (v x - q x))
  have heq (x : ℝ) : (v x - q x) ^ 2 = v x ^ 2 - 2 * (v x * q x) + q x ^ 2 := by ring
  simp_rw [heq] at hnonneg
  have hq2 : IntervalIntegrable (fun x => q x ^ 2) volume 0 π :=
    (show Continuous (fun x => q x ^ 2) from by fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hv2.sub (hvq.const_mul 2))
       hq2,
    intervalIntegral.integral_sub hv2 (hvq.const_mul 2),
    intervalIntegral.integral_const_mul, hvqeq, hqq] at hnonneg
  have hb : (∑ j ∈ s, c j ^ 2) * π ≤
      2 * ∫ x in (0 : ℝ)..π, v x ^ 2 := by nlinarith
  exact ((le_div_iff₀ pi_pos).mpr hb).trans_eq (by ring)

end NLAlib
