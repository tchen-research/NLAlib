import TroppMatrixConcentration.Defs.Probability
import TroppMatrixConcentration.Defs.Dilation
import Mathlib.Analysis.Convex.Function
import TroppMatrixConcentration.Ch6.IndependentSumSecondMoment

/-!
# Equation 2.2.5 — Additivity of matrix variance

Lean name: `TroppMatrixConcentration.variance_additivity`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Section 2.2.7, equation (2.2.5), printed pp. 27–28.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

open TroppMatrixConcentration

theorem TroppMatrixConcentration.variance_additivity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hL2 : ∀ k, MemLp (X k) 2 μ) (hIndep : iIndepFun X μ) :
    (∫ ω, ((∑ k, X k ω) - ∫ ω', ∑ k, X k ω' ∂μ) ^ 2 ∂μ) =
      ∑ k, ∫ ω, (X k ω - ∫ ω', X k ω' ∂μ) ^ 2 ∂μ := by
  classical
  set c : Fin N → Matrix (Fin d) (Fin d) ℂ := fun k => ∫ ω', X k ω' ∂μ with hc
  set Y : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ := fun k ω => X k ω - c k with hY
  have hXint : ∀ k, Integrable (X k) μ := fun k => (hL2 k).integrable one_le_two
  have hsum : ∀ ω, (∑ k, X k ω) - ∫ ω', ∑ k, X k ω' ∂μ = ∑ k, Y k ω := by
    intro ω
    rw [integral_finsetSum _ (fun k _ => hXint k), ← Finset.sum_sub_distrib]
  have hYMeas : ∀ k, Measurable (Y k) := fun k => (hMeas k).sub_const _
  have hYIndep : iIndepFun Y μ :=
    hIndep.comp (fun k (x : Matrix (Fin d) (Fin d) ℂ) => x - c k)
      (fun k => measurable_id.sub_const _)
  have hYL2 : ∀ k, MemLp (fun ω => id (Y k ω)) 2 μ := fun k =>
    (hL2 k).sub (memLp_const (c k))
  have hYMean : ∀ k, (∫ ω, id (Y k ω) ∂μ) = 0 := by
    intro k
    simp only [id, hY]
    rw [integral_sub (hXint k) (integrable_const _), integral_const]
    simp [hc]
  have key := ch6_independent_sum_second_moment μ Y id id measurable_id measurable_id
    hYMeas hYIndep hYL2 hYL2 hYMean
  simp only [id] at key
  simp_rw [hsum, sq]
  exact key
