import NLAlib.ForMathlib.MeasureTheory.IntervalSupport
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

/-! # Weak convergence for tests continuous on a common support interval

A continuous function on the common compact support can be extended to a
bounded continuous function by clamping to that interval. Weak convergence
then gives convergence of the actual integrals, without requiring any
regularity of the original test function outside the supports.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

/-- Weak convergence of real probability laws on a common compact interval
implies convergence of every real or complex test integral continuous on that
interval. The approximating support condition is only eventual. -/
theorem tendsto_integral_of_support_subset_Icc {I 𝕜 : Type*} [RCLike 𝕜]
    {l : Filter I} {μs : I → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hweak : Tendsto μs l (𝓝 μ)) {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ᶠ i in l, (μs i : Measure ℝ).support ⊆ Icc a b)
    (hμ : (μ : Measure ℝ).support ⊆ Icc a b) {f : ℝ → 𝕜}
    (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun i => ∫ x, f x ∂(μs i : Measure ℝ)) l
      (𝓝 (∫ x, f x ∂(μ : Measure ℝ))) := by
  let F : C(Icc a b, 𝕜) := ⟨fun x => f x, continuousOn_iff_continuous_domRestrict.mp hf⟩
  let G : ℝ →ᵇ 𝕜 := (BoundedContinuousFunction.mkOfCompact F).compContinuous
    ⟨projIcc a b hab, continuous_projIcc⟩
  have hG (x : ℝ) (hx : x ∈ Icc a b) : G x = f x := by
    change f (projIcc a b hab x) = f x
    rw [projIcc_of_mem hab hx]
  have hEq (ν : Measure ℝ) (hν : ν.support ⊆ Icc a b) :
      (∫ x, G x ∂ν) = ∫ x, f x ∂ν :=
    integral_congr_ae ((ν.ae_mem_Icc_of_support_subset hν).mono hG)
  have h := (tendsto_iff_forall_integral_rclike_tendsto 𝕜).mp hweak G
  rw [hEq (μ : Measure ℝ) hμ] at h
  apply h.congr'
  filter_upwards [hs] with i hi
  exact hEq (μs i : Measure ℝ) hi

end MeasureTheory.ProbabilityMeasure
