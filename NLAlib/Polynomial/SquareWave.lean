import NLAlib.ForMathlib.Analysis.FourierCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Data.Real.Sign

/-!
# Square-wave orthogonality for sharp Jackson

The sign of the `N`-th sine is invariant under a `2π/N` shift. Haar integral invariance
then forces every nonzero Fourier coefficient of frequency below `N` to vanish.
-/

noncomputable section

open Complex MeasureTheory Real
open scoped Topology Real ComplexConjugate

namespace NLAlib

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The periodic sine square wave on the additive circle.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
def jacksonSquareWaveCircle (N : ℕ) (t : AddCircle (2 * Real.pi)) : ℝ :=
  Real.sign ((fourier (N : ℤ) t).im)

/-- At a real angle the square wave is exactly `sign(sin(Nt))`.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
theorem jacksonSquareWaveCircle_coe_eq (N : ℕ) (t : ℝ) :
    jacksonSquareWaveCircle N (t : AddCircle (2 * Real.pi)) = Real.sign (Real.sin ((N : ℝ) * t)) := by
  rw [jacksonSquareWaveCircle, im_fourier_nat_coe_eq_sin]

/-- The actual square wave is measurable.
Source: the piecewise real sign function; helper for sharp `jackson-lipschitz`. -/
theorem measurable_jacksonSquareWaveCircle (N : ℕ) : Measurable (jacksonSquareWaveCircle N) := by
  have hm : Measurable (fun t : AddCircle (2 * Real.pi) => (fourier (N : ℤ) t).im) :=
    Complex.continuous_im.measurable.comp (fourier (N : ℤ)).continuous.measurable
  unfold jacksonSquareWaveCircle Real.sign
  exact Measurable.ite (measurableSet_lt hm measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const hm) measurable_const measurable_const)

/-- The square-wave modulus is bounded by one.
Source: the piecewise real sign function; helper for sharp `jackson-lipschitz`. -/
theorem abs_jacksonSquareWaveCircle_le_one (N : ℕ) (t : AddCircle (2 * Real.pi)) :
    |jacksonSquareWaveCircle N t| ≤ 1 := by
  unfold jacksonSquareWaveCircle
  rcases Real.sign_apply_eq (fourier (N : ℤ) t).im with h | h | h <;>
    rw [h] <;> norm_num

/-- The square wave is integrable under normalized circle Haar measure.
Source: bounded measurable functions on a probability space; helper for sharp `jackson-lipschitz`. -/
theorem integrable_jacksonSquareWaveCircle (N : ℕ) :
    Integrable (jacksonSquareWaveCircle N) AddCircle.haarAddCircle := by
  have hm : MemLp (jacksonSquareWaveCircle N) 1 AddCircle.haarAddCircle :=
    MemLp.of_bound (measurable_jacksonSquareWaveCircle N).aestronglyMeasurable 1
      (ae_of_all _ fun t => by simpa only [Real.norm_eq_abs] using abs_jacksonSquareWaveCircle_le_one N t)
  exact hm.integrable le_rfl

/-- A uniform `N`-grid shift leaves the actual square wave unchanged.
Source: operator rederivations `rt:sawtooth`; helper for sharp `jackson-lipschitz`. -/
theorem jacksonSquareWaveCircle_add_div_period (N : ℕ) (hN : 0 < N)
    (t : AddCircle (2 * Real.pi)) :
    jacksonSquareWaveCircle N (t + ((2 * Real.pi / N : ℝ) : AddCircle (2 * Real.pi))) =
      jacksonSquareWaveCircle N t := by
  rw [jacksonSquareWaveCircle, fourier_apply_add, fourier_nat_div_period_eq_one N hN, mul_one]
  rfl

/-- Low nonzero Fourier coefficients of the actual square wave vanish exactly.
Source: operator rederivations `rt:sawtooth`; Haar shift invariance and roots of unity.
Atlas `jackson-lipschitz` (orthogonality helper). -/
theorem fourierCoeff_jacksonSquareWaveCircle_eq_zero {N k : ℕ} (hk : 0 < k) (hkN : k < N) :
    fourierCoeff (fun t : AddCircle (2 * Real.pi) => (jacksonSquareWaveCircle N t : ℂ)) (k : ℤ) = 0 := by
  let a : AddCircle (2 * Real.pi) := (2 * Real.pi / N : ℝ)
  let f : AddCircle (2 * Real.pi) → ℂ := fun t =>
    fourier (-(k : ℤ)) t • (jacksonSquareWaveCircle N t : ℂ)
  have hc : fourier (-(k : ℤ)) a ≠ 1 := by
    rw [fourier_neg]
    intro heq
    have h := congrArg (starRingEnd ℂ) heq
    exact fourier_nat_div_period_ne_one hk hkN (by simpa [a] using h)
  have hshift : ∀ t, f (t + a) = fourier (-(k : ℤ)) a * f t := by
    intro t
    change fourier (-(k : ℤ)) (t + a) * (jacksonSquareWaveCircle N (t + a) : ℂ) =
      fourier (-(k : ℤ)) a * (fourier (-(k : ℤ)) t * (jacksonSquareWaveCircle N t : ℂ))
    rw [fourier_apply_add, jacksonSquareWaveCircle_add_div_period N (hk.trans hkN)]
    ring
  have h := MeasureTheory.integral_add_right_eq_self f a (μ := AddCircle.haarAddCircle)
  simp_rw [hshift] at h
  rw [MeasureTheory.integral_const_mul] at h
  change fourier (-(k : ℤ)) a * fourierCoeff (fun t : AddCircle (2 * Real.pi) =>
    (jacksonSquareWaveCircle N t : ℂ)) (k : ℤ) =
    fourierCoeff (fun t : AddCircle (2 * Real.pi) => (jacksonSquareWaveCircle N t : ℂ)) (k : ℤ) at h
  have hzero : (fourier (-(k : ℤ)) a - 1) *
      fourierCoeff (fun t : AddCircle (2 * Real.pi) => (jacksonSquareWaveCircle N t : ℂ)) (k : ℤ) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hc)

/-- The bounded measurable Fourier character times the square wave is interval integrable.
Source: bounded measurable functions on a finite interval; helper for sharp `jackson-lipschitz`. -/
theorem intervalIntegrable_fourier_mul_jacksonSquareWaveCircle (N : ℕ) (k : ℤ) :
    IntervalIntegrable (fun t : ℝ => fourier k (t : AddCircle (2 * Real.pi)) *
      (jacksonSquareWaveCircle N (t : AddCircle (2 * Real.pi)) : ℂ)) volume 0 (2 * Real.pi) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
  have hc : Measurable (fun t : ℝ => fourier k (t : AddCircle (2 * Real.pi))) :=
    ((fourier k).continuous.comp (by fun_prop)).measurable
  have hs : Measurable (fun t : ℝ => (jacksonSquareWaveCircle N (t : AddCircle (2 * Real.pi)) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp ((measurable_jacksonSquareWaveCircle N).comp (by fun_prop))
  apply Integrable.of_bound (hc.mul hs).aestronglyMeasurable 1
  exact ae_of_all _ fun t => by
    change ‖fourier k (t : AddCircle (2 * Real.pi)) *
      (jacksonSquareWaveCircle N (t : AddCircle (2 * Real.pi)) : ℂ)‖ ≤ 1
    rw [norm_mul, show ‖fourier k (t : AddCircle (2 * Real.pi))‖ = 1 from Circle.norm_coe _, one_mul]
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      abs_jacksonSquareWaveCircle_le_one N (t : AddCircle (2 * Real.pi))

/-- The actual real sine square wave is interval integrable over a full period.
Source: bounded measurable functions on a finite interval; helper for sharp `jackson-lipschitz`. -/
theorem intervalIntegrable_sign_sin (N : ℕ) :
    IntervalIntegrable (fun t : ℝ => Real.sign (Real.sin ((N : ℝ) * t))) volume 0 (2 * Real.pi) := by
  have h := intervalIntegrable_fourier_mul_jacksonSquareWaveCircle N 0
  have hreal : IntervalIntegrable (fun t : ℝ =>
      (fourier 0 (t : AddCircle (2 * Real.pi)) *
        (jacksonSquareWaveCircle N (t : AddCircle (2 * Real.pi)) : ℂ)).re)
      volume 0 (2 * Real.pi) :=
    ⟨Complex.reCLM.integrable_comp h.1, Complex.reCLM.integrable_comp h.2⟩
  simpa only [fourier_zero, one_mul, Complex.ofReal_re, jacksonSquareWaveCircle_coe_eq] using hreal

/-- The actual sine square wave is orthogonal on a full period to every positive sine
frequency below `N`. The proof transports the proved Fourier cancellation through its
normalized interval integral and imaginary-part projection.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem integral_sign_sin_mul_sin_eq_zero {N k : ℕ} (hk : 0 < k) (hkN : k < N) :
    (∫ t : ℝ in 0..2 * Real.pi, Real.sign (Real.sin ((N : ℝ) * t)) * Real.sin ((k : ℝ) * t)) = 0 := by
  let f : ℝ → ℂ := fun t => fourier (-(k : ℤ)) (t : AddCircle (2 * Real.pi)) *
    (jacksonSquareWaveCircle N (t : AddCircle (2 * Real.pi)) : ℂ)
  have hcoef := fourierCoeff_jacksonSquareWaveCircle_eq_zero hk hkN
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add] at hcoef
  simp only [Complex.real_smul, smul_eq_mul] at hcoef
  have hfactor : (((1 / (2 * Real.pi) : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0)
  have hInt : (∫ t in 0..2 * Real.pi, f t) = 0 :=
    (mul_eq_zero.mp hcoef).resolve_left hfactor
  have hf := intervalIntegrable_fourier_mul_jacksonSquareWaveCircle N (-(k : ℤ))
  have hproj := Complex.imCLM.intervalIntegral_comp_comm hf
  change (∫ t in 0..2 * Real.pi, (f t).im) = (∫ t in 0..2 * Real.pi, f t).im at hproj
  rw [hInt, Complex.zero_im] at hproj
  have hterm : ∀ t : ℝ, (f t).im =
      -(Real.sign (Real.sin ((N : ℝ) * t)) * Real.sin ((k : ℝ) * t)) := by
    intro t
    change (fourier (-(k : ℤ)) (t : AddCircle (2 * Real.pi)) *
      (jacksonSquareWaveCircle N (t : AddCircle (2 * Real.pi)) : ℂ)).im = _
    rw [fourier_neg]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im,
      im_fourier_nat_coe_eq_sin, jacksonSquareWaveCircle_coe_eq, mul_zero, zero_add]
    ring
  simp_rw [hterm] at hproj
  rw [intervalIntegral.integral_neg] at hproj
  exact neg_eq_zero.mp hproj

end NLAlib
