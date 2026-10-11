import NLAlib.Concentration.Matrix.Martingale.LocalSecondMoment
import NLAlib.ForMathlib.Analysis.Matrix.Order

/-!
# Finite trace budgets make genuine local moments integrable

Coordinate-vector extended moment identities supply integrability of every column
square. Their sum dominates the operator norm square, with coefficient one.
-/

noncomputable section

open MeasureTheory Matrix Finset Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {Ω n : Type*} {m mΩ : MeasurableSpace Ω} [Fintype n] [DecidableEq n]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A finite deterministic trace budget makes the genuine local variance and actual
increment square integrable. The equality of extended moments is the only second-moment
assumption. Source: supplied audit `audit:combined`, coordinate-basis reduction;
helper for `matrix-freedman`. -/
theorem HasLocalMatrixSecondMoment.integrable_and_integrable_sq_of_trace_le
    {X V : Ω → Matrix n n ℂ} (h : HasLocalMatrixSecondMoment μ m X V)
    (hm : m ≤ mΩ) (hX : Measurable X) {b : ℝ}
    (hb : ∀ᵐ ω ∂μ, (V ω).trace.re ≤ b) :
    Integrable V μ ∧ Integrable (fun ω => X ω ^ 2) μ := by
  have hVmeas : Measurable V := h.measurable.mono hm le_rfl
  have hVI : Integrable V μ := (integrable_const b).mono' hVmeas.aestronglyMeasurable (by
    filter_upwards [h.ae_posSemidef, hb] with ω hp hbω
    exact (norm_le_re_trace_of_posSemidef _ hp).trans hbω)
  have hcol : ∀ j : n, Integrable (fun ω => ∑ i, ‖X ω i j‖ ^ 2) μ := by
    intro j
    have hqmeas : Measurable (fun ω => (V ω j j).re) :=
      (Complex.continuous_re.comp (continuous_id.matrix_elem j j)).measurable.comp hVmeas
    have hq0 : 0 ≤ᵐ[μ] fun ω => (V ω j j).re :=
      h.ae_posSemidef.mono fun ω hp => (RCLike.nonneg_iff.mp hp.diag_nonneg).1
    have hqI : Integrable (fun ω => (V ω j j).re) μ :=
      (integrable_const b).mono' hqmeas.aestronglyMeasurable (by
        filter_upwards [h.ae_posSemidef, hb, hq0] with ω hp hbω h0
        rw [Real.norm_of_nonneg h0]
        apply le_trans ?_ hbω
        change (V ω j j).re ≤ (∑ i, V ω i i).re
        rw [Complex.re_sum]
        exact Finset.single_le_sum
          (fun i _ => (RCLike.nonneg_iff.mp (hp.diag_nonneg (i := i))).1) (mem_univ j))
    have hExt := h.setLIntegral_eq (Pi.single j 1) Set.univ MeasurableSet.univ
    simp only [Measure.restrict_univ, matrixVectorSqNorm_single,
      matrixQuadraticFormReal_single] at hExt
    have hmeas : AEStronglyMeasurable (fun ω => ∑ i, ‖X ω i j‖ ^ 2) μ := by
      exact (Finset.measurable_sum univ (fun i _ =>
        ((continuous_id.matrix_elem i j).measurable.comp hX).norm.pow_const 2)).aestronglyMeasurable
    have h0 : 0 ≤ᵐ[μ] fun ω => ∑ i, ‖X ω i j‖ ^ 2 :=
      ae_of_all μ fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine ⟨hmeas, (hasFiniteIntegral_iff_ofReal h0).mpr ?_⟩
    rw [hExt]
    exact (hasFiniteIntegral_iff_ofReal hq0).mp hqI.hasFiniteIntegral
  have hsum : Integrable (fun ω => ∑ j, ∑ i, ‖X ω i j‖ ^ 2) μ :=
    integrable_finsetSum _ fun j _ => hcol j
  have hX2meas : AEStronglyMeasurable (fun ω => X ω ^ 2) μ :=
    (hX.pow_const 2).aestronglyMeasurable
  refine ⟨hVI, hsum.mono' hX2meas ?_⟩
  apply ae_of_all
  intro ω
  calc
    ‖X ω ^ 2‖ ≤ ‖X ω‖ ^ 2 := by simpa only [sq] using norm_mul_le (X ω) (X ω)
    _ ≤ ∑ i, ∑ j, ‖X ω i j‖ ^ 2 := norm_sq_le_sum_sq_norm_entries _
    _ = ∑ j, ∑ i, ‖X ω i j‖ ^ 2 := Finset.sum_comm

end NLAlib
