import NLAlib.ForMathlib.Analysis.Complex.CubicalCauchyFormula
import NLAlib.ForMathlib.Topology.CubicalMaps

/-! # Changing the domain subtype of an actual contour chain

Continuous inclusion of planar domains leaves each ambient native path
unchanged. Consequently native curve integrals and winding integrals are
preserved by the checked continuous chain pushforward.
-/

noncomputable section
open scoped unitInterval
namespace Complex

/-- An inclusion of planar domain subtypes preserves the native contour
integral of every finite signed chain, with no integrability premise needed. -/
theorem cubicalCurveIntegral_mapOne_inclusion {Ω Θ : Set ℂ} (h : Ω ⊆ Θ)
    (g : ℂ → ℂ) (Γ : Cubical.OneChain Ω) :
    cubicalCurveIntegral g (Cubical.mapOne (ContinuousMap.inclusion h) Γ) =
      cubicalCurveIntegral g Γ := by
  have he : (cubicalCurveIntegral g).comp (Cubical.mapOne (ContinuousMap.inclusion h)) =
      cubicalCurveIntegral g := by
    apply Finsupp.lhom_ext
    intro γ k
    simp only [LinearMap.comp_apply, Cubical.mapOne_single, cubicalCurveIntegral,
      Finsupp.linearCombination_single]
    rfl
  exact LinearMap.congr_fun he Γ

/-- An inclusion of planar domain subtypes preserves the actual winding
integral, including the target and normalization. -/
theorem cubicalWindingIntegral_mapOne_inclusion {Ω Θ : Set ℂ} (h : Ω ⊆ Θ)
    (Γ : Cubical.OneChain Ω) (τ : ℂ) :
    cubicalWindingIntegral (Cubical.mapOne (ContinuousMap.inclusion h) Γ) τ =
      cubicalWindingIntegral Γ τ := by
  simp only [cubicalWindingIntegral, cubicalCurveIntegral_mapOne_inclusion]

end Complex
