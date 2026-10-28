import NLAlib.ForMathlib.MeasureTheory.CompactKantorovich
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Compactly supported Wasserstein bounds compose

The already proved compact Kantorovich theorem and the elementary lower bound
from Lipschitz observables give a triangle bound for the primal transport cost.
-/

noncomputable section
open MeasureTheory Set
namespace NLAlib
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

omit [SecondCountableTopology X] in
/-- A primal transport bound controls every observable Lipschitz on the common
compact support. McShane extension avoids any assumptions outside that support. -/
theorem integral_sub_le_of_wassersteinEDistOne_le_of_ae_mem_compact
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : Set X} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ x ∂ν, x ∈ K)
    {C : ℝ} (hC : 0 ≤ C) (hW : wassersteinEDistOne μ ν ≤ ENNReal.ofReal C)
    {f : X → ℝ} (hf : LipschitzOnWith 1 f K) :
    (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤ C := by
  obtain ⟨g,hg,hfg⟩ := hf.extend_real
  have hi (m : Measure X) [IsFiniteMeasure m] (hm : ∀ᵐ x ∂m, x ∈ K) : Integrable g m := by
    have hh := hg.continuous.continuousOn.integrableOn_compact (μ := m) hK
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hm] at hh
  have hh := (enorm_integral_sub_le_wassersteinEDistOne hg (hi μ hμ) (hi ν hν)).trans hW
  rw [← ofReal_norm] at hh
  have hn := (ENNReal.ofReal_le_ofReal_iff hC).mp hh
  have hEq (m : Measure X) (hm : ∀ᵐ x ∂m, x ∈ K) :
      (∫ x, f x ∂m) = ∫ x, g x ∂m :=
    integral_congr_ae (hm.mono fun x hx => hfg hx)
  rw [hEq μ hμ, hEq ν hν]
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hn)

/-- Compact support suffices for a real triangle bound on the infimum over
actual couplings; neither law needs a density. -/
theorem wassersteinEDistOne_le_add_of_ae_mem_compact
    (μ ν ξ : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ξ] {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ x ∂ν, x ∈ K) (hξ : ∀ᵐ x ∂ξ, x ∈ K)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hμν : wassersteinEDistOne μ ν ≤ ENNReal.ofReal C)
    (hνξ : wassersteinEDistOne ν ξ ≤ ENNReal.ofReal D) :
    wassersteinEDistOne μ ξ ≤ ENNReal.ofReal (C+D) := by
  apply wassersteinEDistOne_le_of_ae_mem_compact_of_lipschitzOn_integral_sub_le
    μ ξ hK hμ hξ (C+D)
  intro f hf
  have h1 := integral_sub_le_of_wassersteinEDistOne_le_of_ae_mem_compact
    μ ν hK hμ hν hC hμν hf
  have h2 := integral_sub_le_of_wassersteinEDistOne_le_of_ae_mem_compact
    ν ξ hK hν hξ hD hνξ hf
  linarith

end NLAlib
