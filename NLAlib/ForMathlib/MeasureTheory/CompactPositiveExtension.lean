import NLAlib.ForMathlib.Analysis.PositiveExtension
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Compact

/-! # Positive measure extensions on compact spaces

A measure's integral functional on any subspace containing the constants has
a positive measure extension minimizing one chosen continuous observable.
The minimum equals the supremum over subspace functions below that observable.
This is the order-extension foundation of compact Kantorovich duality.
-/

noncomputable section

open MeasureTheory Set CompactlySupported

namespace NLAlib

/-- On a compact space, prescribing integrals on a subspace containing all
constants admits a finite positive measure which minimizes a chosen continuous
cost. The minimum is exactly the supremum of the integrals of the minorants
from that subspace. The original finite measure supplies consistent data. -/
theorem exists_finiteMeasure_integral_eq_sSup_of_submodule
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [BorelSpace X] [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (V : Submodule ℝ C(X, ℝ)) (hconst : ∀ r : ℝ, ContinuousMap.const X r ∈ V)
    (cost : C(X, ℝ)) :
    ∃ π : Measure X, IsFiniteMeasure π ∧
      (∀ F : C(X, ℝ), F ∈ V → ∫ x, F x ∂π = ∫ x, F x ∂μ) ∧
      (∫ x, cost x ∂π) =
        sSup ((fun F : C(X, ℝ) => ∫ x, F x ∂μ) '' {F ∈ V | F ≤ cost}) := by
  have hI (F : C(X, ℝ)) : Integrable F μ :=
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  let f : C(X, ℝ) →ₗ.[ℝ] ℝ :=
    ⟨V, { toFun := fun F => ∫ x, F.val x ∂μ
          map_add' := fun F G => integral_add (hI F.val) (hI G.val)
          map_smul' := fun r F => integral_smul r F.val }⟩
  let s : PointedCone ℝ C(X, ℝ) :=
    { carrier := {F | ∀ x, 0 ≤ F x}
      zero_mem' := fun _ => le_rfl
      add_mem' := fun hF hG x => add_nonneg (hF x) (hG x)
      smul_mem' := fun r F hF x => mul_nonneg r.property (hF x) }
  have hpos (F : f.domain) (hF : (F : C(X, ℝ)) ∈ s) :
      0 ≤ f F := integral_nonneg (fun x => hF x)
  have hdense (F : C(X, ℝ)) : ∃ G : f.domain,
      (G : C(X, ℝ)) + F ∈ s := by
    refine ⟨⟨ContinuousMap.const X ‖F‖, hconst ‖F‖⟩, ?_⟩
    intro x
    change 0 ≤ ‖F‖ + F x
    linarith [F.neg_norm_le_apply x]
  obtain ⟨g, hgf, hg, hcost⟩ := exists_extension_nonneg_apply_eq_sSup
    s f cost hpos hdense
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun F => g F.toContinuousMap
      map_add' := fun F G => g.map_add F.toContinuousMap G.toContinuousMap
      map_smul' := fun r F => g.map_smul r F.toContinuousMap
      monotone' := by
        intro F G hFG
        apply sub_nonneg.mp
        rw [← g.map_sub]
        apply hg
        exact fun x => sub_nonneg.mpr (hFG x) }
  let π := RealRMK.rieszMeasure Λ
  have hrepr (F : C(X, ℝ)) : ∫ x, F x ∂π = g F := by
    exact RealRMK.integral_rieszMeasure Λ
      (CompactlySupportedContinuousMap.continuousMapEquiv F)
  refine ⟨π, inferInstance, ?_, ?_⟩
  · intro F hF
    exact (hrepr F).trans (hgf ⟨F, hF⟩)
  · rw [hrepr cost, hcost]
    congr 1
    ext t
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact ⟨F.val, ⟨F.property, fun x => sub_nonneg.mp (hF x)⟩, rfl⟩
    · rintro ⟨F, ⟨hF, hle⟩, rfl⟩
      exact ⟨⟨F, hF⟩, (fun x => sub_nonneg.mpr (hle x)), rfl⟩

end NLAlib
