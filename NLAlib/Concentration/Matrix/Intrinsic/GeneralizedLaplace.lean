import NLAlib.Concentration.Matrix.Defs.IntrinsicDimension
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Proposition 7.4.1 — Generalized matrix Laplace transform

Main declaration: `NLAlib.measure_lambdaMax_ge_le_integral_traceFunction_div`.

Atlas: `intrinsic-dimension`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 7.4.1, printed p. 112.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace NLAlib

private lemma traceFunction_eq_sum {d : ℕ} (φ : ℝ → ℝ)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    traceFunction φ A = ∑ i, φ (hA.eigenvalues i) := by
  rw [traceFunction, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp

/-- For Hermitian `B`, `ψ ≥ 0`, `ψ` monotone on `[0,∞)`, `0 ≤ t ≤ λmax B`:
`ψ t ≤ tr ψ(B)`. -/
private lemma pointwise_bound {d : ℕ} [NeZero d] (ψ : ℝ → ℝ)
    (hNonneg : ∀ x, 0 ≤ ψ x) (hMono : MonotoneOn ψ (Set.Ici 0))
    (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian) (t : ℝ) (ht : 0 ≤ t)
    (htB : t ≤ lambdaMax B) : ψ t ≤ traceFunction ψ B := by
  rw [traceFunction_eq_sum ψ B hB]
  have hn : (Set.range hB.eigenvalues).Nonempty := Set.range_nonempty _
  have hf : (Set.range hB.eigenvalues).Finite := Set.finite_range _
  have hmax : lambdaMax B ∈ Set.range hB.eigenvalues := by
    simpa only [lambdaMax, hB.spectrum_real_eq_range_eigenvalues] using hn.csSup_mem hf
  obtain ⟨i, hi⟩ := hmax
  rw [← hi] at htB
  calc ψ t ≤ ψ (hB.eigenvalues i) :=
        hMono (Set.mem_Ici.mpr ht) (Set.mem_Ici.mpr (ht.trans htB)) htB
    _ ≤ ∑ j, ψ (hB.eigenvalues j) :=
        Finset.single_le_sum (fun j _ => hNonneg (hB.eigenvalues j)) (Finset.mem_univ i)

end NLAlib

open NLAlib

/-- Generalized matrix Laplace transform bound: for `ψ ≥ 0` nondecreasing on `[0, ∞)` and `ψ t > 0`,
`P{λmax(Y) ≥ t} ≤ 𝔼 tr ψ(Y) / ψ t`.

Tropp 2015, Prop. 7.4.1. Atlas: `intrinsic-dimension`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 7*.

The measurability hypothesis is not used by the proof; it is kept to match the source's standing
assumptions. -/
theorem NLAlib.measure_lambdaMax_ge_le_integral_traceFunction_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (Y : Ω → Matrix (Fin d) (Fin d) ℂ) (ψ : ℝ → ℝ)
    (_hMeas : Measurable Y) (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hNonneg : ∀ x, 0 ≤ ψ x) (hMono : MonotoneOn ψ (Set.Ici 0))
    (hInt : Integrable (fun ω => traceFunction ψ (Y ω)) μ)
    (t : ℝ) (ht : 0 ≤ t) (hψt : 0 < ψ t) :
    (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
      (∫ ω, traceFunction ψ (Y ω) ∂μ) / ψ t := by
  have hpos : ∀ᵐ ω ∂μ, (0 : ℝ) ≤ traceFunction ψ (Y ω) := by
    filter_upwards [hHerm] with ω hω
    rw [traceFunction_eq_sum ψ _ hω]
    exact Finset.sum_nonneg (fun j _ => hNonneg _)
  have hs : ∀ᵐ ω ∂μ, ω ∈ {ω | t ≤ lambdaMax (Y ω)} →
      ω ∈ {ω | ψ t ≤ traceFunction ψ (Y ω)} := by
    filter_upwards [hHerm] with ω hω h
    exact pointwise_bound ψ hNonneg hMono _ hω t ht h
  have hsub : μ {ω | t ≤ lambdaMax (Y ω)} ≤ μ {ω | ψ t ≤ traceFunction ψ (Y ω)} :=
    measure_mono_ae hs
  have hreal : (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
      (μ {ω | ψ t ≤ traceFunction ψ (Y ω)}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) hsub
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hpos hInt (ψ t)
  rw [measureReal_def] at hmarkov
  rw [le_div_iff₀ hψt, mul_comm]
  exact (mul_le_mul_of_nonneg_left hreal hψt.le).trans hmarkov
