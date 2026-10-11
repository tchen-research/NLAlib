import NLAlib.Polynomial.SawtoothSquareWave
import NLAlib.ForMathlib.Algebra.Intervals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact L1 norm of the sharp Jackson sawtooth error

The sign identity is proved on every uniform grid cell, the actual interpolant is
annihilated by sine orthogonality, and affine interval integrals give `π²/(n+1)` exactly.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real MeasureTheory Set
open scoped Topology Interval

namespace NLAlib

/-- The full-period endpoint of the uniform sawtooth grid is exactly `2π`.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothGridAngle_two_mul (n : ℕ) :
    sawtoothGridAngle n (2 * (n + 1)) = 2 * Real.pi := by
  unfold sawtoothGridAngle
  push_cast
  field_simp

/-- Full-period reflection reverses the uniform grid index.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothGridAngle_reflection (n j : ℕ) (hj : j ≤ 2 * (n + 1)) :
    sawtoothGridAngle n (2 * (n + 1) - j) = 2 * Real.pi - sawtoothGridAngle n j := by
  unfold sawtoothGridAngle
  rw [Nat.cast_sub hj]
  push_cast
  field_simp

/-- All full-period grid points lie in `[0,2π]`.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothGridAngle_mem_Icc_full {n j : ℕ} (hj : j ≤ 2 * (n + 1)) :
    sawtoothGridAngle n j ∈ Icc (0 : ℝ) (2 * Real.pi) := by
  constructor
  · unfold sawtoothGridAngle; positivity
  · have h := (strictMono_sawtoothGridAngle n).monotone hj
    rwa [sawtoothGridAngle_two_mul] at h

/-- The proved sine-square-wave sign identity holds on every full-period grid cell.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem abs_sawtoothError_eq_sign_sin_mul_on_full_grid_cell (n j : ℕ)
    (hj : j < 2 * (n + 1)) {t : ℝ}
    (ht : t ∈ Ioo (sawtoothGridAngle n j) (sawtoothGridAngle n (j + 1))) :
    |sawtoothError n t| = Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * sawtoothError n t := by
  rcases le_or_gt j n with hjn | hjn
  · exact abs_sawtoothError_eq_sign_sin_mul_on_grid_cell n j hjn ht
  · let k := 2 * (n + 1) - 1 - j
    have hk : k ≤ n := by dsimp [k]; omega
    have hk0 : k = 2 * (n + 1) - (j + 1) := by dsimp [k]; omega
    have hk1 : k + 1 = 2 * (n + 1) - j := by dsimp [k]; omega
    have hleft : sawtoothGridAngle n k = 2 * Real.pi - sawtoothGridAngle n (j + 1) := by
      rw [hk0]
      exact sawtoothGridAngle_reflection n (j + 1) (by omega)
    have hright : sawtoothGridAngle n (k + 1) = 2 * Real.pi - sawtoothGridAngle n j := by
      rw [hk1]
      exact sawtoothGridAngle_reflection n j hj.le
    have hmirror : 2 * Real.pi - t ∈ Ioo (sawtoothGridAngle n k) (sawtoothGridAngle n (k + 1)) := by
      rw [hleft, hright]
      constructor <;> linarith [ht.1, ht.2]
    have h := abs_sawtoothError_eq_sign_sin_mul_on_grid_cell n k hk hmirror
    rw [sawtoothError_two_pi_sub, sign_sin_nat_two_pi_sub, abs_neg, neg_mul_neg] at h
    exact h

/-- Restricting an integrable full-period function to a uniform grid cell preserves
integrability.
Source: interval-integral monotonicity; helper for sharp `jackson-lipschitz`. -/
theorem intervalIntegrable_sawtooth_grid_cell {f : ℝ → ℝ} {n j : ℕ}
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) (hj : j < 2 * (n + 1)) :
    IntervalIntegrable f volume (sawtoothGridAngle n j) (sawtoothGridAngle n (j + 1)) := by
  apply hf.mono_set'
  rw [uIoc_of_le (strictMono_sawtoothGridAngle n (show j < j + 1 by omega)).le,
    uIoc_of_le Real.two_pi_pos.le]
  exact Ioc_subset_Ioc (sawtoothGridAngle_mem_Icc_full hj.le).1
    (sawtoothGridAngle_mem_Icc_full (by omega)).2

/-- Splitting a full-period integral along the actual uniform grid.
Source: interval-integral additivity; helper for sharp `jackson-lipschitz`. -/
theorem sum_integral_sawtooth_grid_eq {f : ℝ → ℝ} (n : ℕ)
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) :
    (∑ j ∈ range (2 * (n + 1)), ∫ t in sawtoothGridAngle n j..sawtoothGridAngle n (j + 1), f t) =
      ∫ t in 0..2 * Real.pi, f t := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := sawtoothGridAngle n) (n := 2 * (n + 1))
    (fun j hj => intervalIntegrable_sawtooth_grid_cell hf hj)
  rw [sawtoothGridAngle_two_mul] at h
  simpa only [sawtoothGridAngle, Nat.cast_zero, zero_mul, zero_div] using h

/-- The full L1 error equals the actual square-wave signed error integral.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem integral_abs_sawtoothError_eq_signed (n : ℕ) :
    (∫ t : ℝ in 0..2 * Real.pi, |sawtoothError n t|) =
      ∫ t : ℝ in 0..2 * Real.pi,
        Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * sawtoothError n t := by
  have hAbs : IntervalIntegrable (fun t : ℝ => |sawtoothError n t|) volume 0 (2 * Real.pi) :=
    ((continuous_sawtoothError n).abs).intervalIntegrable _ _
  have hSigned := (intervalIntegrable_sign_sin (n + 1)).mul_continuousOn
    (continuous_sawtoothError n).continuousOn
  rw [← sum_integral_sawtooth_grid_eq n hAbs, ← sum_integral_sawtooth_grid_eq n hSigned]
  apply sum_congr rfl
  intro j hj
  apply intervalIntegral.integral_congr_Ioo_of_le
    (strictMono_sawtoothGridAngle n (show j < j + 1 by omega)).le
  intro t ht
  exact abs_sawtoothError_eq_sign_sin_mul_on_full_grid_cell n j (mem_range.mp hj) ht

/-- The signed sawtooth error integral reduces to the affine sawtooth integral, because
the actual sine interpolant is orthogonal to the square wave.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem integral_signed_sawtoothError_eq_affine (n : ℕ) :
    (∫ t : ℝ in 0..2 * Real.pi, Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * sawtoothError n t) =
      ∫ t : ℝ in 0..2 * Real.pi, Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * (Real.pi - t) := by
  have hσ := intervalIntegrable_sign_sin (n + 1)
  have hcB : Continuous (fun t : ℝ => Real.pi - t) := continuous_const.sub continuous_id
  have hB := hσ.mul_continuousOn hcB.continuousOn
  have hcτ : Continuous (sawtoothApprox n) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_sawtoothApprox n t).continuousAt)
  have hστ := hσ.mul_continuousOn hcτ.continuousOn
  have hterm : ∀ t : ℝ,
      Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * sawtoothError n t =
        Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * (Real.pi - t) -
          Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * sawtoothApprox n t := by
    intro t
    unfold sawtoothError
    ring
  simp_rw [hterm]
  rw [intervalIntegral.integral_sub hB hστ, integral_sign_sin_mul_sawtoothApprox_eq_zero, sub_zero]

/-- The square-wave affine integral has the exact value `π²/(n+1)`.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem integral_sign_sin_mul_pi_sub_eq (n : ℕ) :
    (∫ t : ℝ in 0..2 * Real.pi, Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * (Real.pi - t)) =
      Real.pi ^ 2 / (n + 1) := by
  have hcB : Continuous (fun t : ℝ => Real.pi - t) := continuous_const.sub continuous_id
  have hf := (intervalIntegrable_sign_sin (n + 1)).mul_continuousOn hcB.continuousOn
  rw [← sum_integral_sawtooth_grid_eq n hf]
  let h := Real.pi / (n + 1)
  have hangle : ∀ j : ℕ, sawtoothGridAngle n j = (j : ℝ) * h := by
    intro j
    unfold sawtoothGridAngle
    dsimp [h]
    ring
  have hcell : ∀ j ∈ range (2 * (n + 1)),
      (∫ t : ℝ in sawtoothGridAngle n j..sawtoothGridAngle n (j + 1),
        Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * (Real.pi - t)) =
      (-1 : ℝ) ^ j * (Real.pi * h - ((j : ℝ) + 1 / 2) * h ^ 2) := by
    intro j hj
    have heq := intervalIntegral.integral_congr_Ioo_of_le (μ := volume)
      (strictMono_sawtoothGridAngle n (show j < j + 1 by omega)).le
      (fun t ht => congrArg (fun s : ℝ => s * (Real.pi - t))
        (sign_sin_mul_eq_neg_one_pow_of_between_grid n j ht))
    rw [heq, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (f := fun _ : ℝ => Real.pi) (g := fun t : ℝ => t)
        (continuous_const.intervalIntegrable _ _)
        (continuous_id.intervalIntegrable _ _), intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    rw [hangle, hangle]
    push_cast
    ring
  rw [Finset.sum_congr rfl hcell]
  rw [sum_alternating_affine_two_mul]
  dsimp [h]
  push_cast
  field_simp

/-- The actual sharp Jackson sawtooth interpolant has the exact L1 error `π²/(n+1)`.
Every construction, sign and orthogonality prerequisite has been proved.
Source: Arnold, numerical analysis, Section 1.2; operator rederivations `rt:sawtooth`.
Atlas `jackson-lipschitz` (kernel-norm helper). -/
theorem integral_abs_sawtoothError_eq (n : ℕ) :
    (∫ t : ℝ in 0..2 * Real.pi, |sawtoothError n t|) = Real.pi ^ 2 / (n + 1) := by
  rw [integral_abs_sawtoothError_eq_signed, integral_signed_sawtoothError_eq_affine,
    integral_sign_sin_mul_pi_sub_eq]

/-- The normalized sharp Jackson kernel error is exactly `π/(2(n+1))`.
Source: Arnold, numerical analysis, Section 1.2; operator rederivations `rt:sawtooth`.
Atlas `jackson-lipschitz` (kernel-norm helper). -/
theorem inv_two_pi_mul_integral_abs_sawtoothError_eq (n : ℕ) :
    (2 * Real.pi)⁻¹ * (∫ t : ℝ in 0..2 * Real.pi, |sawtoothError n t|) =
      Real.pi / (2 * (n + 1)) := by
  rw [integral_abs_sawtoothError_eq]
  field_simp

end NLAlib
