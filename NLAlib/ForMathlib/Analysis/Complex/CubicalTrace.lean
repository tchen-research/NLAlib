import NLAlib.ForMathlib.Analysis.Complex.CubicalCauchy
import Mathlib.Topology.Order.Compact

/-! # The compact trace and actual maximum norm of a finite contour chain

The trace is the finite union of the images of its active continuous edges.
The maximum norm uses zero for the empty chain and is an actual attained
maximum on every nonempty trace. Corners and stationary points are allowed.
-/

noncomputable section
open Set Finset
open scoped unitInterval
namespace Complex

/-- The actual ambient trace of all nonzero edges in a finite signed chain. -/
def cubicalTrace {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) : Set ℂ :=
  ⋃ γ ∈ Γ.support, range (fun r : I => (γ r : ℂ))

/-- Every point of an active edge belongs to the actual contour trace. -/
theorem mem_cubicalTrace {Ω : Set ℂ} {Γ : Cubical.OneChain Ω}
    {γ : C(I, Ω)} (hγ : γ ∈ Γ.support) (r : I) : (γ r : ℂ) ∈ cubicalTrace Γ := by
  exact mem_iUnion.mpr ⟨γ, mem_iUnion.mpr ⟨hγ, mem_range_self r⟩⟩

/-- The actual trace is compact, without any differentiability requirement. -/
theorem isCompact_cubicalTrace {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) :
    IsCompact (cubicalTrace Γ) :=
  Γ.support.isCompact_biUnion (fun γ _ =>
    isCompact_range (continuous_subtype_val.comp γ.continuous))

/-- The trace of a chain in a domain lies in that actual domain. -/
theorem cubicalTrace_subset {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) : cubicalTrace Γ ⊆ Ω := by
  intro z hz
  obtain ⟨γ, hz⟩ := mem_iUnion.mp hz
  obtain ⟨_, r, rfl⟩ := mem_iUnion.mp hz
  exact (γ r).property

/-- The actual maximum norm on the compact contour trace, with value zero
for the empty trace. Continuity on the trace ensures finiteness and attainment. -/
def cubicalMaxNorm {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) (f : ℂ → ℂ) : ℝ :=
  sSup (insert 0 ((fun z => ‖f z‖) '' cubicalTrace Γ))

private theorem bddAbove_insert_norm_image_cubicalTrace {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) {f : ℂ → ℂ} (hf : ContinuousOn f (cubicalTrace Γ)) :
    BddAbove (insert 0 ((fun z => ‖f z‖) '' cubicalTrace Γ)) :=
  bddAbove_insert.mpr ((isCompact_cubicalTrace Γ).bddAbove_image hf.norm)

/-- The actual maximum norm is nonnegative, including an empty contour. -/
theorem cubicalMaxNorm_nonneg {Ω : Set ℂ} (Γ : Cubical.OneChain Ω)
    {f : ℂ → ℂ} (hf : ContinuousOn f (cubicalTrace Γ)) : 0 ≤ cubicalMaxNorm Γ f :=
  le_csSup (bddAbove_insert_norm_image_cubicalTrace Γ hf) (mem_insert 0 _)

/-- The actual maximum norm bounds every integrand value on the trace. -/
theorem norm_le_cubicalMaxNorm {Ω : Set ℂ} (Γ : Cubical.OneChain Ω)
    {f : ℂ → ℂ} (hf : ContinuousOn f (cubicalTrace Γ)) {z : ℂ} (hz : z ∈ cubicalTrace Γ) :
    ‖f z‖ ≤ cubicalMaxNorm Γ f :=
  le_csSup (bddAbove_insert_norm_image_cubicalTrace Γ hf) (mem_insert_of_mem 0 (mem_image_of_mem _ hz))

/-- On every nonempty contour trace the maximum norm is attained at an
actual point of the trace. -/
theorem exists_norm_eq_cubicalMaxNorm {Ω : Set ℂ} (Γ : Cubical.OneChain Ω)
    {f : ℂ → ℂ} (hf : ContinuousOn f (cubicalTrace Γ)) (hΓ : (cubicalTrace Γ).Nonempty) :
    ∃ z ∈ cubicalTrace Γ, ‖f z‖ = cubicalMaxNorm Γ f := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_cubicalTrace Γ).exists_isMaxOn hΓ hf.norm
  refine ⟨z, hz, le_antisymm (norm_le_cubicalMaxNorm Γ hf hz) ?_⟩
  unfold cubicalMaxNorm
  apply csSup_le (Set.insert_nonempty 0 _)
  intro v hv
  rcases mem_insert_iff.mp hv with rfl | hv
  · exact norm_nonneg _
  · obtain ⟨w, hw, rfl⟩ := hv
    exact hmax hw

end Complex
