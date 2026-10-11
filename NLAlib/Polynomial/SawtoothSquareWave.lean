import NLAlib.Polynomial.SawtoothSign
import NLAlib.Polynomial.SquareWave
import NLAlib.Polynomial.SineBasis

/-!
# The square-wave dual identity for sawtooth interpolation

The sign on every uniform grid cell is explicit, and low-frequency sine orthogonality
annihilates the actual finite sine interpolant. These are the finite integral ingredients
for the exact sharp Jackson kernel norm.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real MeasureTheory
open scoped Topology

namespace NLAlib

/-- The sine square wave is the alternating constant on every uniform grid cell.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sign_sin_mul_eq_neg_one_pow_of_between_grid (n j : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ioo (sawtoothGridAngle n j) (sawtoothGridAngle n (j + 1))) :
    Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) = (-1 : ℝ) ^ j := by
  let u := ((n + 1 : ℕ) : ℝ) * t - (j : ℝ) * Real.pi
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hleft := ht.1
  have hright := ht.2
  simp only [sawtoothGridAngle, Nat.cast_add, Nat.cast_one] at hleft hright
  rw [div_lt_iff₀ hN] at hleft
  rw [lt_div_iff₀ hN] at hright
  have hu : u ∈ Set.Ioo (0 : ℝ) Real.pi := by
    dsimp [u]
    push_cast
    constructor <;> nlinarith
  have hs := sin_pos_of_pos_of_lt_pi hu.1 hu.2
  have hphase : ((n + 1 : ℕ) : ℝ) * t = u + (j : ℝ) * Real.pi := by dsimp [u]; ring
  rw [hphase, sin_add_nat_mul_pi]
  rcases neg_one_pow_eq_or ℝ j with h | h
  · rw [h, one_mul, Real.sign_of_pos hs]
  · rw [h, neg_one_mul, Real.sign_neg, Real.sign_of_pos hs]

/-- The absolute sawtooth error equals its sine-square-wave signed value on the positive
half-period cells.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem abs_sawtoothError_eq_sign_sin_mul_on_grid_cell (n j : ℕ) (hj : j ≤ n) {t : ℝ}
    (ht : t ∈ Set.Ioo (sawtoothGridAngle n j) (sawtoothGridAngle n (j + 1))) :
    |sawtoothError n t| = Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * sawtoothError n t := by
  rw [sign_sin_mul_eq_neg_one_pow_of_between_grid n j ht]
  exact abs_sawtoothError_eq_mul_on_grid_cell n j hj ht

/-- The sine square wave changes sign under full-period reflection.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sign_sin_nat_two_pi_sub (N : ℕ) (t : ℝ) :
    Real.sign (sin ((N : ℝ) * (2 * Real.pi - t))) = -Real.sign (sin ((N : ℝ) * t)) := by
  rw [mul_sub, sin_nat_mul_two_pi_sub, Real.sign_neg]

/-- A bounded sine times the sine square wave is interval integrable on a full period.
Source: bounded measurable functions on a finite interval; helper for sharp `jackson-lipschitz`. -/
theorem intervalIntegrable_sign_sin_mul_sin (N k : ℕ) :
    IntervalIntegrable (fun t : ℝ => Real.sign (sin ((N : ℝ) * t)) * sin ((k : ℝ) * t))
      volume 0 (2 * Real.pi) := by
  have h := intervalIntegrable_fourier_mul_jacksonSquareWaveCircle N (-(k : ℤ))
  have hi : IntervalIntegrable (fun t : ℝ =>
      (fourier (-(k : ℤ)) (t : AddCircle (2 * Real.pi)) *
        (jacksonSquareWaveCircle N (t : AddCircle (2 * Real.pi)) : ℂ)).im)
      volume 0 (2 * Real.pi) :=
    ⟨Complex.imCLM.integrable_comp h.1, Complex.imCLM.integrable_comp h.2⟩
  have hterm : ∀ t : ℝ,
      (fourier (-(k : ℤ)) (t : AddCircle (2 * Real.pi)) *
        (jacksonSquareWaveCircle N (t : AddCircle (2 * Real.pi)) : ℂ)).im =
        -(Real.sign (sin ((N : ℝ) * t)) * sin ((k : ℝ) * t)) := by
    intro t
    rw [fourier_neg]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im,
      im_fourier_nat_coe_eq_sin, jacksonSquareWaveCircle_coe_eq, mul_zero, zero_add]
    ring
  simp_rw [hterm] at hi
  have hneg := hi.neg
  change IntervalIntegrable (fun t : ℝ => -(-(Real.sign (sin ((N : ℝ) * t)) * sin ((k : ℝ) * t))))
    volume 0 (2 * Real.pi) at hneg
  simpa only [neg_neg] using hneg

/-- The actual sawtooth sine interpolant is orthogonal to the sine square wave of its
next frequency. Its finite sine expansion is proved, not assumed.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem integral_sign_sin_mul_sawtoothApprox_eq_zero (n : ℕ) :
    (∫ t : ℝ in 0..2 * Real.pi, Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * sawtoothApprox n t) = 0 := by
  obtain ⟨c, hc⟩ := exists_sine_expansion_sawtoothApprox n
  simp_rw [hc, mul_sum]
  have hfun : ∀ j ∈ range n, (fun t : ℝ =>
      Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * (c j * sin (((j + 1 : ℕ) : ℝ) * t))) =
      (fun t : ℝ => c j * (Real.sign (sin (((n + 1 : ℕ) : ℝ) * t)) * sin (((j + 1 : ℕ) : ℝ) * t))) := by
    intro j hj
    funext t
    ring
  rw [intervalIntegral.integral_finsetSum (fun j hj => by
    rw [hfun j hj]
    exact (intervalIntegrable_sign_sin_mul_sin (n + 1) (j + 1)).const_mul (c j))]
  apply sum_eq_zero
  intro j hj
  rw [hfun j hj, intervalIntegral.integral_const_mul,
    integral_sign_sin_mul_sin_eq_zero (by omega) (by have := mem_range.mp hj; omega), mul_zero]

end NLAlib
