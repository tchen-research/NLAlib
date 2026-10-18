import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.Holder

/-!
# Covariance and variance bounds without independence

Cauchy--Schwarz for centered real variables gives the sharp variance bound
for a sum from separate quadratic budgets, including zero budgets.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}

/-- Cauchy--Schwarz bounds a real covariance by the product of the standard
deviations. No independence is assumed. -/
theorem covariance_le_sqrt_variance_mul_sqrt_variance
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ≤ Real.sqrt (Var[X; μ]) * Real.sqrt (Var[Y; μ]) := by
  let f := fun ω => X ω - ∫ x, X x ∂μ
  let g := fun ω => Y ω - ∫ x, Y x ∂μ
  have hf : MemLp f 2 μ := hX.sub (memLp_const _)
  have hg : MemLp g 2 μ := hY.sub (memLp_const _)
  have hfg : Integrable (fun ω => f ω * g ω) μ := hf.integrable_mul hg
  have hfgabs : Integrable (fun ω => ‖f ω‖ * ‖g ω‖) μ := hf.norm.integrable_mul hg.norm
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp f (ENNReal.ofReal 2) μ by simpa using hf)
    (show MemLp g (ENNReal.ofReal 2) μ by simpa using hg)
  have hpoint (ω : Ω) : f ω * g ω ≤ ‖f ω‖ * ‖g ω‖ := by
    simpa only [Real.norm_eq_abs, abs_mul] using le_abs_self (f ω * g ω)
  have hle := (integral_mono hfg hfgabs hpoint).trans hc
  rw [variance_eq_integral hX.aemeasurable, variance_eq_integral hY.aemeasurable]
  simpa only [covariance, f, g, Real.rpow_two, ← Real.sqrt_eq_rpow,
    Real.norm_eq_abs, sq_abs] using hle

/-- Separate variance budgets imply the sharp sum budget. This includes zero
variance, zero weights and fully correlated variables. -/
theorem variance_add_le_mul_sq_add_of_le_mul_sq
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) {c a b : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hVX : Var[X; μ] ≤ c * a ^ 2) (hVY : Var[Y; μ] ≤ c * b ^ 2) :
    Var[fun ω => X ω + Y ω; μ] ≤ c * (a + b) ^ 2 := by
  have hx : Real.sqrt (Var[X; μ]) ≤ Real.sqrt c * a := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) ha, ?_⟩
    simpa only [mul_pow, Real.sq_sqrt hc] using hVX
  have hy : Real.sqrt (Var[Y; μ]) ≤ Real.sqrt c * b := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) hb, ?_⟩
    simpa only [mul_pow, Real.sq_sqrt hc] using hVY
  have hcov := (covariance_le_sqrt_variance_mul_sqrt_variance hX hY).trans
    (mul_le_mul hx hy (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ha))
  rw [variance_fun_add hX hY]
  have hs := Real.sq_sqrt hc
  nlinarith

end ProbabilityTheory
