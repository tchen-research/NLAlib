import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Independent replacement for nonnegative additive tests

Pointwise one-summand inequalities extend to finite independent product laws.
Tonelli, rather than a moment assumption on intermediate hybrid sums, justifies
each replacement. The supported additive subgroup records, for example, the
Hermitian offsets at which a matrix comparison is valid.
-/

noncomputable section

open MeasureTheory Finset

namespace MeasureTheory

/-- Tonelli's head/tail decomposition for a finite independent product law. -/
theorem lintegral_pi_fin_succ {E : Type*} [MeasurableSpace E] {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, SigmaFinite (μ i)]
    (f : (Fin (n + 1) → E) → ENNReal) (hf : Measurable f) :
    (∫⁻ x, f x ∂Measure.pi μ) =
      ∫⁻ a, ∫⁻ x, f (Fin.cons a x) ∂Measure.pi (fun i => μ i.succ) ∂μ 0 := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm
  have he := (measurePreserving_piFinSuccAbove μ 0).symm
  calc
    _ = ∫⁻ p : E × (Fin n → E), f (e p)
        ∂(μ 0).prod (Measure.pi (fun i => μ i.succ)) := by
      symm
      exact he.lintegral_comp hf
    _ = _ := by
      change (∫⁻ p : E × (Fin n → E), (f ∘ e) p
        ∂(μ 0).prod (Measure.pi (fun i => μ i.succ))) = _
      rw [lintegral_prod _ (hf.comp e.measurable).aemeasurable]
      simp only [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero, cast_eq]

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- One-summand comparison at every offset in an additive subgroup extends to
finite independent sums supported on that subgroup. The test is nonnegative
and may have infinite expectation, so no integrability of hybrid sums is assumed. -/
theorem lintegral_add_sum_apply_pi_le_of_lintegral_add_apply_le {n : ℕ}
    (ν γ : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, IsProbabilityMeasure (γ i)] (S : AddSubgroup E)
    (X Y : Fin n → E → E) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hν : ∀ i, ∀ᵐ x ∂ν i, X i x ∈ S) (hγ : ∀ i, ∀ᵐ x ∂γ i, Y i x ∈ S)
    (f : E → ENNReal) (hf : Measurable f)
    (hstep : ∀ i A, A ∈ S → (∫⁻ x, f (A + X i x) ∂ν i) ≤ ∫⁻ x, f (A + Y i x) ∂γ i)
    (A : E) (hA : A ∈ S) :
    (∫⁻ x, f (A + ∑ i, X i (x i)) ∂Measure.pi ν) ≤
      ∫⁻ x, f (A + ∑ i, Y i (x i)) ∂Measure.pi γ := by
  induction n generalizing A with
  | zero => simp
  | succ n ih =>
    rw [lintegral_pi_fin_succ ν _ (by fun_prop),
      lintegral_pi_fin_succ γ _ (by fun_prop)]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    calc
      _ ≤ ∫⁻ a, ∫⁻ x, f (A + X 0 a + ∑ i, Y i.succ (x i))
          ∂Measure.pi (fun i : Fin n => γ i.succ) ∂ν 0 := by
        apply lintegral_mono_ae
        filter_upwards [hν 0] with a ha
        simpa only [add_assoc] using ih (fun i => ν i.succ) (fun i => γ i.succ)
          (fun i => X i.succ) (fun i => Y i.succ) (fun i => hX i.succ) (fun i => hY i.succ)
          (fun i => hν i.succ) (fun i => hγ i.succ)
          (fun i => hstep i.succ) (A + X 0 a) (S.add_mem hA ha)
      _ = ∫⁻ x, ∫⁻ a, f ((A + ∑ i, Y i.succ (x i)) + X 0 a) ∂ν 0
          ∂Measure.pi (fun i : Fin n => γ i.succ) := by
        rw [lintegral_lintegral_swap (by fun_prop)]
        congr 1
        funext x
        congr 1
        funext a
        congr 1
        abel
      _ ≤ ∫⁻ x, ∫⁻ a, f ((A + ∑ i, Y i.succ (x i)) + Y 0 a) ∂γ 0
          ∂Measure.pi (fun i : Fin n => γ i.succ) := by
        apply lintegral_mono_ae
        have hs : ∀ᵐ x ∂Measure.pi (fun i : Fin n => γ i.succ), ∀ i, Y i.succ (x i) ∈ S :=
          ae_all_iff.mpr (fun i => (Measure.tendsto_eval_ae_ae
            (μ := fun i : Fin n => γ i.succ)).eventually (hγ i.succ))
        filter_upwards [hs] with x hx
        exact hstep 0 _ (S.add_mem hA (S.sum_mem (fun i _ => hx i)))
      _ = _ := by
        rw [lintegral_lintegral_swap (by fun_prop)]
        congr 1
        funext a
        congr 1
        funext x
        congr 1
        abel

end MeasureTheory
