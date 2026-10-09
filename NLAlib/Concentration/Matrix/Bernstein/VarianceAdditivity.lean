import NLAlib.Concentration.Matrix.Defs.Probability
import NLAlib.Concentration.Matrix.Defs.Dilation
import Mathlib.Analysis.Convex.Function
import NLAlib.Concentration.Matrix.Bernstein.IndependentSumSecondMoment

/-!
# Equation 2.2.5 — Additivity of matrix variance

Main declaration: `NLAlib.variance_additivity`.

Atlas: `matrix-bernstein` (variance of an independent sum).

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Section 2.2.7, equation (2.2.5), printed pp. 27–28.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

open NLAlib

/-- The matrix variance of an independent sum of square-integrable random matrices is the sum of their
variances.

Tropp 2015, §2.2.7, eq. (2.2.5). Atlas: `matrix-bernstein`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 6*.

The Hermitian hypothesis is not used by the proof; it is kept to match the source's setting. -/
theorem NLAlib.variance_additivity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : ∀ k, Measurable (X k))
    (_hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
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
  have key := integral_sum_mul_sum_eq_sum_integral_mul μ Y id id measurable_id measurable_id
    hYMeas hYIndep hYL2 hYL2 hYMean
  simp only [id] at key
  simp_rw [hsum, sq]
  exact key
