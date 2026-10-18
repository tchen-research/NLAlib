import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Gaussian exponential moments and central symmetry

Gaussian measures have every linear exponential norm moment, even after a
polynomial norm weight. Centered Gaussian measures are invariant under negation.
The results include singular covariance and are used for BMV replacement.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- Every Gaussian measure has an integrable exponential of any real multiple
of the norm. This follows from Fernique's square-exponential moment and does
not require a nonsingular covariance. -/
theorem integrable_exp_mul_norm (μ : Measure E) [IsGaussian μ] (a : ℝ) :
    Integrable (fun x : E => Real.exp (a * ‖x‖)) μ := by
  obtain ⟨C, hC, hi⟩ := exists_integrable_exp_sq μ
  have hb : ∀ r : ℝ, a * r ≤ C * r ^ 2 + a ^ 2 / (4 * C) := by
    intro r
    have hsq := sq_nonneg (r - a / (2 * C))
    field_simp at hsq ⊢
    nlinarith
  refine (hi.const_mul (Real.exp (a ^ 2 / (4 * C)))).mono'
    (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa only [add_comm] using hb ‖x‖)

/-- The Gaussian exponential norm moment is square-integrable at every real
parameter, allowing Hölder's inequality with any finite polynomial moment. -/
theorem memLp_two_exp_mul_norm (μ : Measure E) [IsGaussian μ] (a : ℝ) :
    MemLp (fun x : E => Real.exp (a * ‖x‖)) 2 μ := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_assoc] using
    integrable_exp_mul_norm μ (2 * a)

/-- A Gaussian norm polynomial multiplied by a linear exponential norm is
integrable at every real exponential parameter and every natural degree. -/
theorem integrable_norm_pow_mul_exp_mul_norm (μ : Measure E) [IsGaussian μ]
    (k : ℕ) (a : ℝ) :
    Integrable (fun x : E => ‖x‖ ^ k * Real.exp (a * ‖x‖)) μ := by
  have hp : MemLp (fun x : E => ‖x‖ ^ k) 2 μ := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    simpa only [← pow_mul, id_eq] using
      (memLp_id μ ((k * 2 : ℕ) : ENNReal) (by finiteness)).integrable_norm_pow'
  exact hp.integrable_mul (memLp_two_exp_mul_norm μ a)

/-- A centered Gaussian measure is invariant under negation, including zero
and singular covariance. -/
theorem map_neg_eq_self_of_integral_eq_zero (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x, x ∂μ = 0) : μ.map (fun x : E => -x) = μ := by
  apply Measure.ext_of_charFunDual
  ext L
  change charFunDual (μ.map ((ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E).toContinuousLinearMap)) L = _
  rw [charFunDual_map]
  rw [charFunDual_eq_of_integral_eq_zero hmean,
    charFunDual_eq_of_integral_eq_zero hmean]
  congr 3
  congr 1
  convert (variance_neg (X := (L : E → ℝ)) (μ := μ)) using 1
  congr 1
  ext x
  simp

/-- Negating the argument of any integrable observable preserves its centered
Gaussian expectation. -/
theorem integral_comp_neg_eq_of_integral_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [IsGaussian μ] (hmean : ∫ x, x ∂μ = 0)
    (f : E → F) (hf : Integrable f μ) :
    (∫ x, f (-x) ∂μ) = ∫ x, f x ∂μ := by
  have hneg := map_neg_eq_self_of_integral_eq_zero μ hmean
  have hfm : AEStronglyMeasurable f (μ.map (fun x : E => -x)) := by
    rw [hneg]
    exact hf.aestronglyMeasurable
  rw [← integral_map (by fun_prop) hfm, hneg]

end ProbabilityTheory.IsGaussian
