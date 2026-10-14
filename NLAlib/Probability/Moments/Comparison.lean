import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Positive real moment comparison

Rooted moments on a probability space are monotone in every positive real exponent,
including exponents below one. This converts Mathlib's extended-valued Lp comparison
to finite Bochner integrals and realizes `positive-real-moment-comparison`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NLAlib

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A finite higher norm moment bounds every rooted positive lower norm moment.
No lower bound of one on the exponents is needed. Source: the positive-real-moment
route in the supplied operator derivations; Mathlib's probability-space Lp comparison. -/
theorem integral_norm_rpow_inv_le {f : Ω → E} (hf : AEStronglyMeasurable f μ)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hq : Integrable (fun ω => ‖f ω‖ ^ q) μ) :
    (∫ ω, ‖f ω‖ ^ p ∂μ) ^ (1 / p) ≤ (∫ ω, ‖f ω‖ ^ q ∂μ) ^ (1 / q) := by
  have hqpos : 0 < q := hp.trans_le hpq
  have hqLp : MemLp f (ENNReal.ofReal q) μ := by
    apply (integrable_norm_rpow_iff hf (by simp [hqpos]) (by simp)).mp
    simpa only [ENNReal.toReal_ofReal hqpos.le] using hq
  have hLp := eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq) hf
  have hreal := ENNReal.toReal_mono hqLp.eLpNorm_ne_top hLp
  rw [toReal_eLpNorm hf, toReal_eLpNorm hf,
    lpNorm_eq_integral_norm_rpow_toReal (by simp [hp]) (by simp) hf,
    lpNorm_eq_integral_norm_rpow_toReal (by simp [hqpos]) (by simp) hf] at hreal
  simpa only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hqpos.le, one_div]
    using hreal

/-- On a probability space, a nonnegative function with finite q moment has finite
p moment and the rooted moments satisfy Lyapunov's inequality for every 0 < p ≤ q.
Source: `open_mathematical_items_operator_derivations`, §1.
atlas: positive-real-moment-comparison -/
theorem integrable_rpow_and_integral_rpow_inv_le {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : Integrable (fun ω => f ω ^ q) μ) :
    Integrable (fun ω => f ω ^ p) μ ∧
      (∫ ω, f ω ^ p ∂μ) ^ (1 / p) ≤ (∫ ω, f ω ^ q ∂μ) ^ (1 / q) := by
  have hnorm : ∀ᵐ ω ∂μ, ‖f ω‖ = f ω := hnonneg.mono fun _ h => Real.norm_of_nonneg h
  have hqnorm : Integrable (fun ω => ‖f ω‖ ^ q) μ :=
    hq.congr (hnorm.mono fun _ h => congrArg (fun x : ℝ => x ^ q) h.symm)
  have hpnorm := integrable_norm_rpow_of_le hf hp.le (hp.trans_le hpq).le hpq hqnorm
  refine ⟨hpnorm.congr (hnorm.mono fun _ h => congrArg (fun x : ℝ => x ^ p) h), ?_⟩
  have h := integral_norm_rpow_inv_le hf hp hpq hqnorm
  simpa only [integral_congr_ae (hnorm.mono fun _ h => congrArg (fun x : ℝ => x ^ p) h),
    integral_congr_ae (hnorm.mono fun _ h => congrArg (fun x : ℝ => x ^ q) h)] using h

end NLAlib
