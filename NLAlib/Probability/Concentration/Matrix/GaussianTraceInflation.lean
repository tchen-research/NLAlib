import NLAlib.ForMathlib.Analysis.Calculus.SecondOrderIntegral

/-!
# The continuous Gaussian replacement inflation

The exact exponential-integral coefficient defines Gaussian trace replacement
at every parameter, including zero. Bernstein's scalar exponential bound gives
the rational upper estimates used to optimize the eigenvalue comparison.
Source: Tropp (2026), Propositions 4.5--4.6 and Section 4.9.
-/

noncomputable section

namespace NLAlib

/-- The exact continuous scalar inflation in one-sided Gaussian replacement.
The integral coefficient gives the removable values at zero automatically. -/
def gaussianTraceInflation (R θ : ℝ) : ℝ :=
  θ * Real.sqrt (2 * expSecondRemainderCoefficient (θ * R))

/-- Zero time has zero Gaussian replacement inflation. -/
@[simp] theorem gaussianTraceInflation_zero_right (R : ℝ) :
    gaussianTraceInflation R 0 = 0 := by simp [gaussianTraceInflation]

/-- A zero upper bound has unit relative Gaussian inflation at every time. -/
@[simp] theorem gaussianTraceInflation_zero_left (θ : ℝ) :
    gaussianTraceInflation 0 θ = θ := by norm_num [gaussianTraceInflation]

/-- The squared Gaussian inflation is the exact second-order integral budget. -/
theorem gaussianTraceInflation_sq_div_two (R θ : ℝ) :
    gaussianTraceInflation R θ ^ 2 / 2 =
      θ ^ 2 * expSecondRemainderCoefficient (θ * R) := by
  rw [gaussianTraceInflation, mul_pow,
    Real.sq_sqrt (mul_nonneg (by norm_num) (expSecondRemainderCoefficient_nonneg _))]
  ring

/-- Gaussian replacement inflation is nonnegative at nonnegative time. -/
theorem gaussianTraceInflation_nonneg (R : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ gaussianTraceInflation R θ :=
  mul_nonneg hθ (Real.sqrt_nonneg _)

/-- For nonnegative time and upper bound the Gaussian replacement scale
dominates the original time parameter. -/
theorem le_gaussianTraceInflation {R θ : ℝ} (hR : 0 ≤ R) (hθ : 0 ≤ θ) :
    θ ≤ gaussianTraceInflation R θ := by
  have hc := one_half_le_expSecondRemainderCoefficient (mul_nonneg hθ hR)
  have hs : 1 ≤ Real.sqrt (2 * expSecondRemainderCoefficient (θ * R)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show
      1 ≤ 2 * expSecondRemainderCoefficient (θ * R) by linarith)
  simpa only [mul_one, gaussianTraceInflation] using mul_le_mul_of_nonneg_left hs hθ

/-- The squared exact Gaussian inflation satisfies the Bernstein rational
budget below its scalar pole. The estimate includes zero parameters.
Source: Tropp (2026), Section 4.9. -/
theorem gaussianTraceInflation_sq_le_div {R θ : ℝ} (hθR : θ * R < 3) :
    gaussianTraceInflation R θ ^ 2 ≤ θ ^ 2 / (1 - θ * R / 3) := by
  have h := mul_le_mul_of_nonneg_left
    (expSecondRemainderCoefficient_le_div hθR) (sq_nonneg θ)
  have heq := gaussianTraceInflation_sq_div_two R θ
  calc
    _ = 2 * (θ ^ 2 * expSecondRemainderCoefficient (θ * R)) := by linarith
    _ ≤ 2 * (θ ^ 2 * ((1 / 2) / (1 - θ * R / 3))) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- The excess Gaussian inflation is at most the exact Bernstein correction.
This is valid at zero time or zero upper bound without division by either.
Source: Tropp (2026), Section 4.9. -/
theorem gaussianTraceInflation_sub_le_div {R θ : ℝ}
    (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3) :
    gaussianTraceInflation R θ - θ ≤ R * θ ^ 2 / (6 * (1 - θ * R / 3)) := by
  have hd : 0 < 1 - θ * R / 3 := by linarith
  have hB : 0 ≤ θ + R * θ ^ 2 / (6 * (1 - θ * R / 3)) := by positivity
  have hid : (θ + R * θ ^ 2 / (6 * (1 - θ * R / 3))) ^ 2 =
      θ ^ 2 / (1 - θ * R / 3) +
        (R * θ ^ 2 / (6 * (1 - θ * R / 3))) ^ 2 := by
    let d := 1 - θ * R / 3
    change (θ + R * θ ^ 2 / (6 * d)) ^ 2 = θ ^ 2 / d + (R * θ ^ 2 / (6 * d)) ^ 2
    field_simp [show d ≠ 0 from hd.ne']
    dsimp [d]
    ring
  have hsq : θ ^ 2 / (1 - θ * R / 3) ≤
      (θ + R * θ ^ 2 / (6 * (1 - θ * R / 3))) ^ 2 := by
    rw [hid]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hg := gaussianTraceInflation_sq_le_div hθR
  have hg0 := gaussianTraceInflation_nonneg R hθ
  nlinarith

end NLAlib
