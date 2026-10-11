import NLAlib.Gaussian.Khintchine
import NLAlib.Concentration.Matrix.Series.RademacherKhintchine
import NLAlib.Concentration.Matrix.Defs.ScalarLaws
import Mathlib.Probability.Independence.Basic

/-!
# Noncommutative Khintchine on arbitrary probability spaces

The joint law of independent Gaussian or Rademacher coefficients transports
the proved canonical polynomial trace bounds. Taking their nonnegative roots
gives exactly the square-root constant from the integer-moment manuscript.
Source: operator manuscript `thm:khintchine`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}

omit [IsProbabilityMeasure μ] in
/-- Independent actual Gaussian or Rademacher coefficients on an arbitrary
probability space obey the exact integer noncommutative trace-moment bound.
All integrability is derived in the canonical law proofs. Source: manuscript
`thm:khintchine`, both coefficient laws. The coefficient index is `Fin n` to
share the Gaussian product-law interface; matrix indices are arbitrary finite
types, including the empty type.
atlas: noncommutative-khintchine -/
theorem integral_re_trace_independent_series_pow_le
    (A : Fin n → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ξ : Fin n → Ω → ℝ) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ)
    (hlaw : (∀ i, IsStandardGaussian μ (ξ i)) ∨ (∀ i, IsRademacher μ (ξ i)))
    {p : ℕ} (hp : 1 ≤ p) :
    (∫ ω, ((∑ i, ξ i ω • A i) ^ (2 * p)).trace.re ∂μ) ≤
      (2 * p - 1 : ℕ) ^ p * ((∑ i, A i ^ 2) ^ p).trace.re := by
  let X := fun ω i => ξ i ω
  let f := fun x : Fin n → ℝ => ((∑ i, x i • A i) ^ (2 * p)).trace.re
  have hX : Measurable X := measurable_pi_lambda _ hξ
  have hf : Continuous f := by
    simpa only [one_mul, pow_zero, mul_one] using
      continuous_re_trace_series_product A 1 1 (2 * p) 0
  have hjoint := hind.map_fun_eq_pi_map (fun i => (hξ i).aemeasurable)
  have hm : (∫ x, f x ∂μ.map X) = ∫ ω, f (X ω) ∂μ :=
    integral_map hX.aemeasurable hf.aestronglyMeasurable
  rcases hlaw with hlaw | hlaw
  · have hprod : μ.map X = Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
      rw [hjoint]
      exact congrArg Measure.pi (funext fun i => hlaw i)
    rw [hprod] at hm
    rw [← hm]
    exact integral_re_trace_gaussianSeries_pow_le A hA hp
  · have hprod : μ.map X = Measure.pi (fun _ : Fin n => rademacherMeasure) := by
      rw [hjoint]
      exact congrArg Measure.pi (funext fun i => hlaw i)
    rw [hprod] at hm
    rw [← hm]
    exact integral_re_trace_rademacherSeries_pow_le A hA hp

omit [IsProbabilityMeasure μ] in
/-- **Integer noncommutative Khintchine, rooted form.** The exact nonnegative
`2p`-th root of the trace moment is bounded by `sqrt(2p-1)` times the variance
trace root, for independent standard Gaussian or Rademacher coefficients.
Source: manuscript `thm:khintchine`. The zero-moment, zero-variance and empty
matrix cases use the same formula, without division by a moment.
atlas: noncommutative-khintchine -/
theorem integral_re_trace_independent_series_pow_rpow_le
    (A : Fin n → Matrix ι ι ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ξ : Fin n → Ω → ℝ) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ)
    (hlaw : (∀ i, IsStandardGaussian μ (ξ i)) ∨ (∀ i, IsRademacher μ (ξ i)))
    {p : ℕ} (hp : 1 ≤ p) :
    (∫ ω, ((∑ i, ξ i ω • A i) ^ (2 * p)).trace.re ∂μ) ^ (1 / (2 * (p : ℝ))) ≤
      Real.sqrt (2 * p - 1 : ℕ) *
        (((∑ i, A i ^ 2) ^ p).trace.re) ^ (1 / (2 * (p : ℝ))) := by
  apply rpow_le_sqrt_mul_rpow_of_nat_pow_le
  · exact integral_nonneg fun ω => re_trace_pow_nonneg_of_even _
      (isHermitian_sum_smul_real A hA (fun i => ξ i ω)) (even_two_mul p)
  · exact re_trace_pow_nonneg_of_posSemidef _ (posSemidef_sum_sq_of_isHermitian A hA) p
  · exact Nat.cast_nonneg _
  · exact hp
  · exact integral_re_trace_independent_series_pow_le A hA ξ hξ hind hlaw hp

end NLAlib
