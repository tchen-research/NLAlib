import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Integrable affine series and finite-product comparison

Integrability of a finite scalar series follows from the first moments of its
coefficients. One-coordinate comparisons of affine norms tensorize to a finite
product. These facts use genuine product measures and Bochner integrals.
-/

noncomputable section
open MeasureTheory Set

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite affine combination of integrable real variables has integrable
norm, in any real normed space. -/
theorem integrable_norm_add_sum_smul {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) (z : E) (a : ι → E) :
    Integrable (fun ω => ‖z + ∑ i, X i ω • a i‖) μ := by
  have hc : Continuous (fun x : ι → ℝ => ‖z + ∑ i, x i • a i‖) := by fun_prop
  have hm : AEMeasurable (fun ω => fun i => X i ω) μ :=
    aemeasurable_pi_lambda _ fun i => (hX i).aemeasurable
  have hi := integrable_finsetSum Finset.univ fun i _ => (hX i).norm.mul_const ‖a i‖
  refine ((integrable_const ‖z‖).add hi).mono'
    (hc.measurable.comp_aemeasurable hm).aestronglyMeasurable ?_
  filter_upwards [] with ω
  change |‖z + ∑ i, X i ω • a i‖| ≤ ‖z‖ + ∑ i, ‖X i ω‖ * ‖a i‖
  rw [abs_of_nonneg (norm_nonneg _)]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  simpa only [norm_smul] using norm_sum_le Finset.univ (fun i => X i ω • a i)

/-- The norm of a finite affine series is integrable under any product of
scalar probability laws with finite first moments. -/
theorem integrable_norm_add_sum_smul_pi {ι : Type*} [Fintype ι]
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (id : ℝ → ℝ) (ν i)) (z : E) (a : ι → E) :
    Integrable (fun x : ι → ℝ => ‖z + ∑ i, x i • a i‖) (Measure.pi ν) :=
  integrable_norm_add_sum_smul (fun i => integrable_eval (hν i)) z a

private theorem integral_fin_succ_norm_sum (n : ℕ)
    (ν : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, Integrable (id : ℝ → ℝ) (ν i)) (z : E) (a : Fin (n + 1) → E) :
    (∫ x : Fin (n + 1) → ℝ, ‖z + ∑ i, x i • a i‖ ∂Measure.pi ν) =
      ∫ t : ℝ, ∫ x : Fin n → ℝ, ‖(z + t • a 0) + ∑ i, x i • a i.succ‖
        ∂Measure.pi (fun i => ν i.succ) ∂ν 0 := by
  let e := (measurePreserving_piFinSuccAbove ν 0).symm
  have hF := integrable_norm_add_sum_smul_pi ν hν z a
  have hi := e.integrable_comp_of_integrable hF
  have he := e.integral_comp' (fun x : Fin (n + 1) → ℝ => ‖z + ∑ i, x i • a i‖)
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.sum_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
    Fin.zero_succAbove, Fin.cons_zero, Function.comp_def, cast_eq, ← add_assoc] at hi he
  simp only [Fin.sum_univ_succ, ← add_assoc]
  rw [← he, integral_prod _ hi]

private theorem integrable_norm_mixed_fin_series (n : ℕ)
    (ν : Measure ℝ) (η : Fin n → Measure ℝ) [IsProbabilityMeasure ν]
    [∀ i, IsProbabilityMeasure (η i)]
    (hν : Integrable (id : ℝ → ℝ) ν) (hη : ∀ i, Integrable (id : ℝ → ℝ) (η i))
    (z : E) (a : Fin (n + 1) → E) :
    Integrable (fun p : ℝ × (Fin n → ℝ) =>
      ‖(z + p.1 • a 0) + ∑ i, p.2 i • a i.succ‖) (ν.prod (Measure.pi η)) := by
  let X : Fin (n + 1) → (ℝ × (Fin n → ℝ)) → ℝ :=
    Fin.cases (fun p => p.1) (fun i p => p.2 i)
  have hX : ∀ i, Integrable (X i) (ν.prod (Measure.pi η)) := by
    refine Fin.cases ?_ (fun i => ?_)
    · exact hν.comp_fst _
    · exact (integrable_eval (hη i)).comp_snd _
  have hi := integrable_norm_add_sum_smul hX z a
  simpa [X, Fin.sum_univ_succ, ← add_assoc] using hi

private theorem integral_norm_add_sum_smul_pi_le_fin (n : ℕ) :
    ∀ (ν η : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
      [∀ i, IsProbabilityMeasure (η i)]
      (hν : ∀ i, Integrable (id : ℝ → ℝ) (ν i))
      (hη : ∀ i, Integrable (id : ℝ → ℝ) (η i)) (a : Fin n → E),
      (∀ i z, (∫ t : ℝ, ‖z + t • a i‖ ∂ν i) ≤ ∫ t : ℝ, ‖z + t • a i‖ ∂η i) →
      ∀ z, (∫ x : Fin n → ℝ, ‖z + ∑ i, x i • a i‖ ∂Measure.pi ν) ≤
        ∫ x : Fin n → ℝ, ‖z + ∑ i, x i • a i‖ ∂Measure.pi η := by
  induction n with
  | zero =>
    intro ν η _ _ hν hη a hstep z
    simp
  | succ n ih =>
    intro ν η _ _ hν hη a hstep z
    have hνν := integrable_norm_mixed_fin_series n (ν 0) (fun i => ν i.succ)
      (hν 0) (fun i => hν i.succ) z a
    have hνη := integrable_norm_mixed_fin_series n (ν 0) (fun i => η i.succ)
      (hν 0) (fun i => hη i.succ) z a
    have hηη := integrable_norm_mixed_fin_series n (η 0) (fun i => η i.succ)
      (hη 0) (fun i => hη i.succ) z a
    calc
      _ = ∫ t : ℝ, ∫ x : Fin n → ℝ, ‖(z + t • a 0) + ∑ i, x i • a i.succ‖
          ∂Measure.pi (fun i => ν i.succ) ∂ν 0 := integral_fin_succ_norm_sum n ν hν z a
      _ ≤ ∫ t : ℝ, ∫ x : Fin n → ℝ, ‖(z + t • a 0) + ∑ i, x i • a i.succ‖
          ∂Measure.pi (fun i => η i.succ) ∂ν 0 := by
        apply integral_mono hνν.integral_prod_left hνη.integral_prod_left
        intro t
        exact ih (fun i => ν i.succ) (fun i => η i.succ) (fun i => hν i.succ)
          (fun i => hη i.succ) (fun i => a i.succ) (fun i => hstep i.succ) (z + t • a 0)
      _ = ∫ x : Fin n → ℝ, ∫ t : ℝ, ‖(z + t • a 0) + ∑ i, x i • a i.succ‖
          ∂ν 0 ∂Measure.pi (fun i => η i.succ) := integral_integral_swap hνη
      _ ≤ ∫ x : Fin n → ℝ, ∫ t : ℝ, ‖(z + t • a 0) + ∑ i, x i • a i.succ‖
          ∂η 0 ∂Measure.pi (fun i => η i.succ) := by
        apply integral_mono hνη.integral_prod_right hηη.integral_prod_right
        intro x
        have h := hstep 0 (z + ∑ i, x i • a i.succ)
        simpa only [add_assoc, add_left_comm, add_comm] using h
      _ = ∫ t : ℝ, ∫ x : Fin n → ℝ, ‖(z + t • a 0) + ∑ i, x i • a i.succ‖
          ∂Measure.pi (fun i => η i.succ) ∂η 0 := (integral_integral_swap hηη).symm
      _ = _ := (integral_fin_succ_norm_sum n η hη z a).symm

/-- Comparisons of all one-coordinate affine norms tensorize to finite scalar
product laws. The offset may be any vector and the coefficients are fixed. -/
theorem integral_norm_add_sum_smul_pi_le {ι : Type*} [Fintype ι]
    (ν η : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, IsProbabilityMeasure (η i)]
    (hν : ∀ i, Integrable (id : ℝ → ℝ) (ν i))
    (hη : ∀ i, Integrable (id : ℝ → ℝ) (η i)) (a : ι → E)
    (hstep : ∀ i z, (∫ t : ℝ, ‖z + t • a i‖ ∂ν i) ≤
      ∫ t : ℝ, ‖z + t • a i‖ ∂η i) (z : E) :
    (∫ x : ι → ℝ, ‖z + ∑ i, x i • a i‖ ∂Measure.pi ν) ≤
      ∫ x : ι → ℝ, ‖z + ∑ i, x i • a i‖ ∂Measure.pi η := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft ν e).integral_comp',
    ← (measurePreserving_piCongrLeft η e).integral_comp']
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp_rw [← e.sum_comp]
  simp only [Equiv.piCongrLeft_apply_apply]
  exact integral_norm_add_sum_smul_pi_le_fin _ (fun i => ν (e i)) (fun i => η (e i))
    (fun i => hν (e i)) (fun i => hη (e i)) (fun i => a (e i)) (fun i => hstep (e i)) z

end MeasureTheory
