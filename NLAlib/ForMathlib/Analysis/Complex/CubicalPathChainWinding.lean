import NLAlib.ForMathlib.Analysis.Complex.CubicalPathChainIntegral
import NLAlib.ForMathlib.Analysis.Complex.CubicalWindingInterval
import NLAlib.ForMathlib.Topology.BoundedComplementFill

/-! # Native positive orientation for finite cornered contour pieces

A single actual normalized inverse integral fixes the positive orientation
on an avoided real interval. Local constancy derives all the other winding
values. Nonzero winding also places those targets in the actual bounded-
complement filled trace, with no supplied Cauchy identity or Jordan theorem.
-/

noncomputable section
open Set
open scoped unitInterval
namespace Complex

/-- Nonzero actual winding forces the target into the trace or one of its
bounded complementary components. -/
theorem mem_boundedComplementFill_cubicalTrace_of_winding_ne_zero
    {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) (hc : Cubical.boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {τ : ℂ} (hw : cubicalWindingIntegral Γ τ ≠ 0) :
    τ ∈ boundedComplementFill (cubicalTrace Γ) := by
  by_contra hnot
  obtain ⟨hoff, hunbounded⟩ := not_mem_boundedComplementFill_iff.mp hnot
  exact hw (cubicalWindingIntegral_eq_zero_of_unbounded_component Γ hc hΓ hoff hunbounded)

/-- One actual native positive-orientation integral of a closed cornered
path determines winding one at every point of an avoided real interval.
The interval may be a singleton, and only the individual pieces are C1. -/
theorem cubicalWindingIntegral_pathChain_eq_one_of_curveIntegral_eq
    {Ω : Set ℂ} {k : ℕ} (p : Fin (k + 1) → Ω)
    (γ : (i : Fin k) → Path (p i.castSucc) (p i.succ))
    (hp : p (Fin.last k) = p 0)
    (hγ : ∀ i, ContDiffOn ℝ 1 ((γ i).map continuous_subtype_val).extend I)
    {a b x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b)
    (hoff : ∀ i r, ∀ x ∈ Icc a b, ((γ i) r : ℂ) ≠ (x : ℂ))
    (hpos : (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      curveIntegral (fun z => (z - (x₀ : ℂ))⁻¹ • ContinuousLinearMap.id ℂ ℂ)
        ((Path.concat p γ).map continuous_subtype_val) = 1) :
    ∀ x ∈ Icc a b, cubicalWindingIntegral (Cubical.pathChain p γ) (x : ℂ) = 1 := by
  have hbase : cubicalWindingIntegral (Cubical.pathChain p γ) (x₀ : ℂ) = 1 := by
    unfold cubicalWindingIntegral
    rw [cubicalCurveIntegral_pathChain_eq_curveIntegral_concat]
    · exact hpos
    · intro i
      have hne : ∀ z ∈ range ((γ i).map continuous_subtype_val), z - (x₀ : ℂ) ≠ 0 := by
        rintro z ⟨r, rfl⟩
        exact sub_ne_zero.mpr (hoff i r x₀ hx₀)
      exact (((continuousOn_id.sub continuousOn_const).inv₀ hne).smul continuousOn_const)
        |>.curveIntegrable_of_contDiffOn (hγ i) (fun r => mem_range_self r)
  intro x hx
  apply (cubicalWindingIntegral_eq_of_mem_real_interval (Cubical.pathChain p γ)
    (Cubical.boundaryOne_pathChain_eq_zero p γ hp)
    (contDiffOn_cubicalPath_of_mem_support_pathChain p γ hγ) hx₀ hx ?_).trans hbase
  intro t ht htrace
  obtain ⟨q, hq⟩ := mem_iUnion.mp htrace
  obtain ⟨hqs, r, hr⟩ := mem_iUnion.mp hq
  obtain ⟨i, rfl⟩ := Cubical.exists_piece_of_mem_support_pathChain p γ hqs
  exact hoff i r t ht hr

end Complex
