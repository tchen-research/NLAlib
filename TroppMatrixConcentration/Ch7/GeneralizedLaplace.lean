import TroppMatrixConcentration.Defs.Ch7Intrinsic
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Proposition 7.4.1 — Generalized matrix Laplace transform

Lean name: `TroppMatrixConcentration.ch7_generalized_laplace`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 7.4.1, printed p. 112.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

lemma ch7_generalized_laplace_traceFunction_eq_sum {d : ℕ} (φ : ℝ → ℝ)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    traceFunction φ A = ∑ i, φ (hA.eigenvalues i) := by
  rw [traceFunction, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp

/-- For Hermitian `B`, `ψ ≥ 0`, `ψ` monotone on `[0,∞)`, `0 ≤ t ≤ λmax B`:
`ψ t ≤ tr ψ(B)`. -/
lemma ch7_generalized_laplace_pointwise {d : ℕ} [NeZero d] (ψ : ℝ → ℝ)
    (hNonneg : ∀ x, 0 ≤ ψ x) (hMono : MonotoneOn ψ (Set.Ici 0))
    (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian) (t : ℝ) (ht : 0 ≤ t)
    (htB : t ≤ lambdaMax B) : ψ t ≤ traceFunction ψ B := by
  rw [ch7_generalized_laplace_traceFunction_eq_sum ψ B hB]
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

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem TroppMatrixConcentration.ch7_generalized_laplace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (Y : Ω → Matrix (Fin d) (Fin d) ℂ) (ψ : ℝ → ℝ)
    (hMeas : Measurable Y) (hHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hNonneg : ∀ x, 0 ≤ ψ x) (hMono : MonotoneOn ψ (Set.Ici 0))
    (hInt : Integrable (fun ω => traceFunction ψ (Y ω)) μ)
    (t : ℝ) (ht : 0 ≤ t) (hψt : 0 < ψ t) :
    (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
      (∫ ω, traceFunction ψ (Y ω) ∂μ) / ψ t := by
  have hpos : ∀ᵐ ω ∂μ, (0 : ℝ) ≤ traceFunction ψ (Y ω) := by
    filter_upwards [hHerm] with ω hω
    rw [ch7_generalized_laplace_traceFunction_eq_sum ψ _ hω]
    exact Finset.sum_nonneg (fun j _ => hNonneg _)
  have hs : ∀ᵐ ω ∂μ, ω ∈ {ω | t ≤ lambdaMax (Y ω)} →
      ω ∈ {ω | ψ t ≤ traceFunction ψ (Y ω)} := by
    filter_upwards [hHerm] with ω hω h
    exact ch7_generalized_laplace_pointwise ψ hNonneg hMono _ hω t ht h
  have hsub : μ {ω | t ≤ lambdaMax (Y ω)} ≤ μ {ω | ψ t ≤ traceFunction ψ (Y ω)} :=
    measure_mono_ae hs
  have hreal : (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
      (μ {ω | ψ t ≤ traceFunction ψ (Y ω)}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) hsub
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hpos hInt (ψ t)
  rw [measureReal_def] at hmarkov
  rw [le_div_iff₀ hψt, mul_comm]
  exact (mul_le_mul_of_nonneg_left hreal hψt.le).trans hmarkov
