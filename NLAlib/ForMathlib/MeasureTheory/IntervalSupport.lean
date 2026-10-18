import Mathlib.MeasureTheory.Measure.Support

/-! # Elementary API for measures supported on a compact real interval -/

open Set
open MeasureTheory

namespace MeasureTheory.Measure

/-- A law whose support is contained in a real interval is almost surely
in that interval. -/
theorem ae_mem_Icc_of_support_subset (μ : Measure ℝ) {a b : ℝ}
    (hsupport : μ.support ⊆ Icc a b) : ∀ᵐ z ∂μ, z ∈ Icc a b :=
  (show ∀ᵐ z ∂μ, z ∈ μ.support from μ.support_mem_ae).mono hsupport

/-- The support of a real interval-supported measure is compact. -/
theorem isCompact_support_of_subset_Icc (μ : Measure ℝ) {a b : ℝ}
    (hsupport : μ.support ⊆ Icc a b) : IsCompact μ.support :=
  isCompact_Icc.of_isClosed_subset μ.isClosed_support hsupport

end MeasureTheory.Measure
