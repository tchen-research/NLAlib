import NLAlib.ForMathlib.Analysis.Complex.CubicalWindingVariation
import Mathlib.Topology.Order.IntermediateValue

/-! # Winding normalization propagates across an avoided interval

Local constancy on the actual trace complement makes winding constant on
every preconnected set of avoided targets. In particular a single positive
orientation normalization determines all targets on a real support interval.
-/

noncomputable section
open Set
open scoped unitInterval
namespace Complex

/-- Actual finite-chain winding is constant on every preconnected set of
targets disjoint from its actual trace. -/
theorem cubicalWindingIntegral_eq_of_isPreconnected {Ω S : Set ℂ}
    (Γ : Cubical.OneChain Ω) (hc : Cubical.boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hS : IsPreconnected S) (hoff : S ⊆ (cubicalTrace Γ)ᶜ)
    {u v : ℂ} (hu : u ∈ S) (hv : v ∈ S) :
    cubicalWindingIntegral Γ u = cubicalWindingIntegral Γ v := by
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hloc := (isLocallyConstant_cubicalWindingIntegral Γ hc hΓ).comp_continuous
    (show Continuous (fun z : S => (⟨z, hoff z.property⟩ : {w : ℂ // w ∉ cubicalTrace Γ}))
      from continuous_subtype_val.subtype_mk _)
  exact hloc.apply_eq_of_preconnectedSpace ⟨u, hu⟩ ⟨v, hv⟩

/-- On an actual real support interval, one winding value determines every
other one. The interval may be a singleton; no interior regularity or
nonzero-derivative assumption is imposed on the contour.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem cubicalWindingIntegral_eq_of_mem_real_interval {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) (hc : Cubical.boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {a b x₀ x : ℝ} (hx₀ : x₀ ∈ Icc a b) (hx : x ∈ Icc a b)
    (hoff : ∀ t ∈ Icc a b, (t : ℂ) ∉ cubicalTrace Γ) :
    cubicalWindingIntegral Γ (x : ℂ) = cubicalWindingIntegral Γ (x₀ : ℂ) := by
  apply cubicalWindingIntegral_eq_of_isPreconnected Γ hc hΓ
    (S := Complex.ofReal '' Icc a b)
    (isPreconnected_Icc.image _ continuous_ofReal.continuousOn)
  · rintro z ⟨t, ht, rfl⟩
    exact hoff t ht
  · exact mem_image_of_mem _ hx
  · exact mem_image_of_mem _ hx₀

end Complex
