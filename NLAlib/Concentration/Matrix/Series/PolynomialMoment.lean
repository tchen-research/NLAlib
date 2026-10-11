import NLAlib.Matrix.TraceYoung
import NLAlib.Concentration.Matrix.Defs.Probability

/-!
# Closing a polynomial trace moment recursion

The deterministic polynomial trace Young inequality absorbs the lower moment
without dividing by the moment. The recursion is a reusable intermediate
hypothesis here; the Gaussian and Rademacher consumers prove it from their
actual coefficient laws.
Source: operator manuscript, final proof of `thm:khintchine`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A genuine lower-moment trace recursion and polynomial trace Young give
the exact integer Khintchine moment constant. Source: the final absorption
argument in manuscript `thm:khintchine`. This is a helper; consumers must
prove `hrec` from their coefficient laws. -/
theorem integral_re_trace_pow_le_of_polynomial_recursion
    (V : Matrix ι ι ℂ) (hV : V.PosSemidef) (Y : Ω → Matrix ι ι ℂ)
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {p : ℕ} (hp : 1 ≤ p)
    (hM : Integrable (fun ω => (Y ω ^ (2 * p)).trace.re) μ)
    (hW : Integrable (fun ω => (V * Y ω ^ (2 * p - 2)).trace.re) μ)
    (hrec : (∫ ω, (Y ω ^ (2 * p)).trace.re ∂μ) ≤
      (2 * p - 1 : ℕ) * ∫ ω, (V * Y ω ^ (2 * p - 2)).trace.re ∂μ) :
    (∫ ω, (Y ω ^ (2 * p)).trace.re ∂μ) ≤
      (2 * p - 1 : ℕ) ^ p * (V ^ p).trace.re := by
  have hpoint : ∀ᵐ ω ∂μ,
      (p : ℝ) * (2 * p - 1 : ℕ) * (V * Y ω ^ (2 * p - 2)).trace.re ≤
      (2 * p - 1 : ℕ) ^ p * (V ^ p).trace.re +
        (p - 1 : ℕ) * (Y ω ^ (2 * p)).trace.re :=
    hY.mono fun ω hω => nat_mul_mul_re_trace_mul_pow_le V (Y ω) hV hω hp
  have hi := integral_mono_ae (hW.const_mul ((p : ℝ) * (2 * p - 1 : ℕ)))
    ((integrable_const _).add (hM.const_mul (p - 1 : ℕ))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (integrable_const _)
    (hM.const_mul (p - 1 : ℕ)), integral_const, integral_const_mul] at hi
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hi
  have hmul := mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hp)
  rw [hcast] at hi
  linarith

end NLAlib
