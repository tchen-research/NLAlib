import NLAlib.ForMathlib.Probability.ResamplingEntropy
import NLAlib.Probability.Concentration.Entropy.EntropyTensorizationNonneg
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product-law random-gradient entropy

The genuine finite-product entropy bound retains the random positive squared
coordinate replacements inside the exponentially weighted expectation.
It is a probability prerequisite for independent-sum spectral universality.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace NLAlib

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]

/-- A genuine random-gradient entropy inequality on an actual finite product
law. Only measurability and boundedness of the observable are assumed. Each
coordinate is independently replaced with its own original marginal law;
the random squared differences stay inside the exponentially weighted expectation.
The finite index type may be empty and `s = 0` is included.
Source: Boucheron--Lugosi--Massart 2013, Chapter 6, by entropy tensorization. -/
theorem entropy_exp_mul_pi_le_sum_integral_update_posPart_sq_of_bounded
    (f : (ι → Ω) → ℝ) (hfm : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M) {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, s * f x * Real.exp (s * f x) ∂Measure.pi ν) -
      (∫ x, Real.exp (s * f x) ∂Measure.pi ν) *
        Real.log (∫ x, Real.exp (s * f x) ∂Measure.pi ν) ≤
      s ^ 2 * ∑ i, ∫ x, ∫ t,
        Real.exp (s * f x) * max (f x - f (Function.update x i t)) 0 ^ 2
          ∂ν i ∂Measure.pi ν := by
  let Y : (ι → Ω) → ℝ := fun x => Real.exp (s * f x)
  let H : ι → (ι → Ω) → ℝ := fun i x => ∫ t,
    Real.exp (s * f x) * max (f x - f (Function.update x i t)) 0 ^ 2 ∂ν i
  have hYm : Measurable Y := by fun_prop
  have hY : Integrable Y (Measure.pi ν) := by
    apply Integrable.of_bound hYm.aestronglyMeasurable (Real.exp (|s| * M))
    apply ae_of_all
    intro x
    simpa only [Y, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_mul_le_exp_abs_mul_of_abs_le (s := s) (hbound x)
  have hYlog : Integrable (fun x => Y x * Real.log (Y x)) (Measure.pi ν) := by
    apply Integrable.of_bound (by fun_prop)
      (Real.exp (|s| * M) * (|s| * M))
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    dsimp [Y]
    rw [Real.log_exp, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
    exact mul_le_mul (Real.exp_mul_le_exp_abs_mul_of_abs_le (hbound x))
      (mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg s))
      (mul_nonneg (abs_nonneg s) (abs_nonneg _)) (Real.exp_pos _).le
  have hHi (i : ι) : Integrable (H i) (Measure.pi ν) := by
    exact (integrable_exp_mul_posPart_sub_sq_of_abs_le
      (μ := (Measure.pi ν).prod (ν i))
      (fun q : (ι → Ω) × Ω => f q.1)
      (fun q : (ι → Ω) × Ω => f (Function.update q.1 i q.2))
      (hfm.comp measurable_fst) (hfm.comp measurable_update') hM
      (fun q => hbound q.1) (fun q => hbound _) s).integral_prod_left
  have ht := entropy_pi_le_sum_integral_entropy_update ν Y hYm
    (fun x => Real.exp_pos _) hY hYlog
  have hlocal (i : ι) (x : ι → Ω) :
      (∫ s, Y (Function.update x i s) * Real.log (Y (Function.update x i s)) ∂ν i) -
        (∫ s, Y (Function.update x i s) ∂ν i) *
          Real.log (∫ s, Y (Function.update x i s) ∂ν i) ≤
        s ^ 2 * ∫ s, H i (Function.update x i s) ∂ν i := by
    have hh := entropy_exp_mul_le_integral_posPart_sq_of_bounded (ν i)
      (fun s => f (Function.update x i s)) (hfm.comp (measurable_update x))
      M hM (fun s => hbound _) hs
    have hU := integrable_exp_mul_posPart_sub_sq_of_abs_le
      (μ := (ν i).prod (ν i))
      (fun q : Ω × Ω => f (Function.update x i q.1))
      (fun q : Ω × Ω => f (Function.update x i q.2))
      (by fun_prop) (by fun_prop) hM (fun q => hbound _) (fun q => hbound _) s
    rw [integral_prod _ hU] at hh
    simpa only [Y, H, Function.update_idem, Real.log_exp, mul_comm, mul_left_comm,
      mul_assoc] using hh
  have hsum : ∑ i, ∫ x,
      ((∫ s, Y (Function.update x i s) * Real.log (Y (Function.update x i s)) ∂ν i) -
        (∫ s, Y (Function.update x i s) ∂ν i) *
          Real.log (∫ s, Y (Function.update x i s) ∂ν i)) ∂Measure.pi ν ≤
      ∑ i, s ^ 2 * ∫ x, H i x ∂Measure.pi ν := by
    apply Finset.sum_le_sum
    intro i _
    have hE := integrable_entropy_update_of_nonneg ν i hYm
      (fun x => (Real.exp_pos _).le) hY hYlog
    have h := integral_mono hE
      ((integrable_integral_update_pi ν i (hHi i)).const_mul (s ^ 2)) (hlocal i)
    rw [integral_const_mul, integral_integral_update_pi ν i (hHi i)] at h
    exact h
  have h := ht.trans hsum
  rw [← Finset.mul_sum] at h
  simpa only [Y, H, Real.log_exp, mul_comm, mul_left_comm, mul_assoc] using h

/-- The random-gradient entropy inequality written with two actual independent
full product samples. The replacement coordinate of the second sample has
exactly the original marginal law, and all integrability is derived. -/
theorem entropy_exp_mul_pi_le_integral_resampling_posPart_sq_of_bounded
    (f : (ι → Ω) → ℝ) (hfm : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M) {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, s * f x * Real.exp (s * f x) ∂Measure.pi ν) -
      (∫ x, Real.exp (s * f x) ∂Measure.pi ν) *
        Real.log (∫ x, Real.exp (s * f x) ∂Measure.pi ν) ≤
      s ^ 2 * ∫ q : (ι → Ω) × (ι → Ω),
        Real.exp (s * f q.1) * ∑ i,
          max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2
            ∂((Measure.pi ν).prod (Measure.pi ν)) := by
  have hK (i : ι) : Integrable (fun q : (ι → Ω) × (ι → Ω) =>
      Real.exp (s * f q.1) * max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2)
      ((Measure.pi ν).prod (Measure.pi ν)) := by
    exact integrable_exp_mul_posPart_sub_sq_of_abs_le
      (fun q : (ι → Ω) × (ι → Ω) => f q.1)
      (fun q : (ι → Ω) × (ι → Ω) => f (Function.update q.1 i (q.2 i)))
      (by fun_prop) (by fun_prop) hM (fun q => hbound q.1) (fun q => hbound _) s
  have he : (∫ q : (ι → Ω) × (ι → Ω),
      Real.exp (s * f q.1) * ∑ i,
        max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2
          ∂((Measure.pi ν).prod (Measure.pi ν))) =
      ∑ i, ∫ x, ∫ t,
        Real.exp (s * f x) * max (f x - f (Function.update x i t)) 0 ^ 2
          ∂ν i ∂Measure.pi ν := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _ => hK i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_prod _ (hK i)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => integral_comp_eval (μ := ν) (i := i)
      (f := fun t => Real.exp (s * f x) * max (f x - f (Function.update x i t)) 0 ^ 2)
      (by
        have ht : Measurable (fun t => f (Function.update x i t)) :=
          hfm.comp (measurable_update x)
        exact (measurable_const.mul (((measurable_const.sub ht).max
          measurable_const).pow_const 2)).aestronglyMeasurable)
  rw [he]
  exact entropy_exp_mul_pi_le_sum_integral_update_posPart_sq_of_bounded
    ν f hfm M hM hbound hs

end Product

end NLAlib
