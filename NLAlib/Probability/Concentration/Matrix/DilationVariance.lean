import NLAlib.Probability.Concentration.Basic.MatrixStatistics
import NLAlib.Probability.Concentration.Basic.MatrixCalculus
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Equation 2.2.10 — Variance statistic under dilation

Main declaration: `NLAlib.hermitianSecondMoment_dilation_eq_rectSecondMoment`.

Atlas: `hermitian-dilation`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Section 2.2.8, equations (2.2.7–10), printed pp. 28–29.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

open NLAlib Matrix

/-- The matrix variance of the Hermitian dilation of a centered rectangular random matrix equals its
rectangular variance statistic.

Tropp 2015, §2.2.8, eq. (2.2.10). Atlas: `hermitian-dilation`. Ported from the Prove2me mission
*An Introduction to Matrix Concentration Inequalities, Ch 6*.

The measurability hypothesis is not used by the proof; it is kept to match the source's standing
assumptions.
atlas: hermitian-dilation -/
theorem NLAlib.hermitianSecondMoment_dilation_eq_rectSecondMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n : ℕ} [NeZero m] [NeZero n]
    (Z : Ω → Matrix (Fin m) (Fin n) ℂ) (_hMeas : Measurable Z)
    (hL2 : MemLp Z 2 μ) :
    hermitianSecondMoment μ (fun ω => dilation (Z ω - ∫ ω', Z ω' ∂μ)) =
      rectSecondMoment μ (fun ω => Z ω - ∫ ω', Z ω' ∂μ) := by
  have hW2 : MemLp (fun ω => Z ω - ∫ ω', Z ω' ∂μ) 2 μ := hL2.sub (memLp_const _)
  have hWsq : Integrable (fun ω => ‖Z ω - ∫ ω', Z ω' ∂μ‖ ^ 2) μ :=
    hW2.integrable_norm_pow (p := 2) two_ne_zero
  have hP : Integrable
      (fun ω => (Z ω - ∫ ω', Z ω' ∂μ) * (Z ω - ∫ ω', Z ω' ∂μ)ᴴ) μ := by
    refine Integrable.mono' hWsq ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · have hc : Continuous (fun X : Matrix (Fin m) (Fin n) ℂ => X * Xᴴ) :=
        continuous_id.matrix_mul continuous_id.matrix_conjTranspose
      exact hc.comp_aestronglyMeasurable hW2.1
    · calc _ ≤ ‖Z ω - ∫ ω', Z ω' ∂μ‖ * ‖(Z ω - ∫ ω', Z ω' ∂μ)ᴴ‖ := l2_opNorm_mul _ _
        _ = _ := by rw [l2_opNorm_conjTranspose, sq]
  have hQ : Integrable
      (fun ω => (Z ω - ∫ ω', Z ω' ∂μ)ᴴ * (Z ω - ∫ ω', Z ω' ∂μ)) μ := by
    refine Integrable.mono' hWsq ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · have hc : Continuous (fun X : Matrix (Fin m) (Fin n) ℂ => Xᴴ * X) :=
        continuous_id.matrix_conjTranspose.matrix_mul continuous_id
      exact hc.comp_aestronglyMeasurable hW2.1
    · rw [l2_opNorm_conjTranspose_mul_self, sq]
  unfold hermitianSecondMoment rectSecondMoment
  simp_rw [dilation_sq]
  rw [integral_fromBlocks_diag μ _ _ hP hQ, norm_fromBlocks_diag]
