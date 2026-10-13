import Mathlib.Probability.HasLaw

/-!
# `HasLaw` from a push-forward identity

`hasLaw_iff_map_eq`: when the target law is nonzero, `HasLaw X ν μ` is equivalent to
`μ.map X = ν` (the push-forward identity forces a.e. measurability).
-/

open MeasureTheory

namespace ProbabilityTheory

/-- For a nonzero law `ν`, `HasLaw X ν μ ↔ μ.map X = ν`: a nonzero push-forward forces `X` to be
a.e. measurable (`AEMeasurable.of_map_ne_zero`). -/
theorem hasLaw_iff_map_eq {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]
    {μ : Measure Ω} {ν : Measure 𝓧} {X : Ω → 𝓧} (hν : ν ≠ 0) :
    HasLaw X ν μ ↔ μ.map X = ν :=
  ⟨fun h => h.map_eq, fun h => ⟨AEMeasurable.of_map_ne_zero (h ▸ hν), h⟩⟩

end ProbabilityTheory
