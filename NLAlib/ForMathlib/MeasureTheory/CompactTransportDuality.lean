import NLAlib.ForMathlib.MeasureTheory.Coupling
import NLAlib.ForMathlib.MeasureTheory.CompactPositiveExtension
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # Compact transport duality

Positive order extension and Riesz representation turn bounds on all additive
continuous potentials into an actual coupling with bounded continuous cost.
No optimal coupling or transport duality hypothesis is assumed.
-/

noncomputable section

open MeasureTheory Set

namespace NLAlib

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

/-- The continuous functions on a product which split into one potential on
each factor. -/
def additivePotentialSubmodule : Submodule ℝ C(X × Y, ℝ) where
  carrier := {F | ∃ f : C(X, ℝ), ∃ g : C(Y, ℝ), ∀ p, F p = f p.1 + g p.2}
  zero_mem' := ⟨0, 0, by intro p; simp⟩
  add_mem' := by
    rintro F G ⟨f, g, hF⟩ ⟨f', g', hG⟩
    refine ⟨f + f', g + g', ?_⟩
    intro p
    simp only [ContinuousMap.add_apply, hF, hG]
    ring
  smul_mem' := by
    rintro r F ⟨f, g, hF⟩
    refine ⟨r • f, r • g, ?_⟩
    intro p
    simp only [ContinuousMap.smul_apply, smul_eq_mul, hF, mul_add]

variable {X Y} [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [T2Space X] [T2Space Y]
  [CompactSpace X] [CompactSpace Y]
  [HasOuterApproxClosed X] [HasOuterApproxClosed Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]

private theorem integrable_continuous_compact {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] (μ : Measure Z)
    [IsFiniteMeasure μ] (f : C(Z, ℝ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

omit [SecondCountableTopology X] in
/-- Compact continuous-cost duality in its upper-bound form: if all continuous
potential pairs dominated by the cost have expectation at most `C`, there is
an actual positive coupling whose expected cost is at most `C`. -/
theorem exists_isCoupling_integral_le_of_potentials_le
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : C(X × Y, ℝ)) (C : ℝ)
    (hdual : ∀ (f : C(X, ℝ)) (g : C(Y, ℝ)),
      (∀ x y, f x + g y ≤ cost (x, y)) → (∫ x, f x ∂μ) + (∫ y, g y ∂ν) ≤ C) :
    ∃ π : Measure (X × Y), π.IsCoupling μ ν ∧
      IsProbabilityMeasure π ∧ (∫ p, cost p ∂π) ≤ C := by
  let V := additivePotentialSubmodule X Y
  have hconst (r : ℝ) : ContinuousMap.const (X × Y) r ∈ V :=
    ⟨ContinuousMap.const X r, 0, by intro p; simp⟩
  obtain ⟨π, hπfinite, hπV, hπcost⟩ :=
    exists_finiteMeasure_integral_eq_sSup_of_submodule (μ.prod ν) V hconst cost
  have : IsFiniteMeasure π := hπfinite
  have hproduct := Measure.isCoupling_prod μ ν
  have hsplit (F : C(X × Y, ℝ)) (f : C(X, ℝ)) (g : C(Y, ℝ))
      (hF : ∀ p, F p = f p.1 + g p.2) :
      (∫ p, F p ∂μ.prod ν) = (∫ x, f x ∂μ) + ∫ y, g y ∂ν := by
    have hf := hproduct.measurePreserving_fst.integrable_comp_of_integrable
      (integrable_continuous_compact μ f)
    have hg := hproduct.measurePreserving_snd.integrable_comp_of_integrable
      (integrable_continuous_compact ν g)
    calc
      (∫ p, F p ∂μ.prod ν) = ∫ p, f p.1 + g p.2 ∂μ.prod ν := integral_congr_ae (ae_of_all _ hF)
      _ = (∫ p, f p.1 ∂μ.prod ν) + ∫ p, g p.2 ∂μ.prod ν := integral_add hf hg
      _ = _ := congrArg₂ (· + ·)
        (hproduct.integral_fst f.continuous.aestronglyMeasurable)
        (hproduct.integral_snd g.continuous.aestronglyMeasurable)
  have hcouple : π.IsCoupling μ ν := by
    constructor
    · apply ext_of_forall_integral_eq_of_IsFiniteMeasure
      intro f
      let F : C(X × Y, ℝ) := f.toContinuousMap.comp ⟨Prod.fst, continuous_fst⟩
      have hFV : F ∈ V := ⟨f.toContinuousMap, 0, by intro p; simp [F]⟩
      calc
        (∫ x, f x ∂π.fst) = ∫ p, F p ∂π :=
          integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable
        _ = ∫ p, F p ∂μ.prod ν := hπV F hFV
        _ = ∫ x, f x ∂μ := by
          simpa using hsplit F f.toContinuousMap 0
            (by intro p; simp [F])
    · apply ext_of_forall_integral_eq_of_IsFiniteMeasure
      intro g
      let G : C(X × Y, ℝ) := g.toContinuousMap.comp ⟨Prod.snd, continuous_snd⟩
      have hGV : G ∈ V := ⟨0, g.toContinuousMap, by intro p; simp [G]⟩
      calc
        (∫ y, g y ∂π.snd) = ∫ p, G p ∂π :=
          integral_map measurable_snd.aemeasurable g.continuous.aestronglyMeasurable
        _ = ∫ p, G p ∂μ.prod ν := hπV G hGV
        _ = ∫ y, g y ∂ν := by
          simpa using hsplit G 0 g.toContinuousMap
            (by intro p; simp [G])
  refine ⟨π, hcouple, hcouple.isProbabilityMeasure, ?_⟩
  rw [hπcost]
  have hnonempty : ((fun F : C(X × Y, ℝ) => ∫ p, F p ∂μ.prod ν) ''
      {F ∈ V | F ≤ cost}).Nonempty :=
    ⟨_, ContinuousMap.const (X × Y) (-‖cost‖),
      ⟨hconst _, fun p => cost.neg_norm_le_apply p⟩, rfl⟩
  apply csSup_le hnonempty
  rintro _ ⟨F, ⟨hFV, hle⟩, rfl⟩
  obtain ⟨f, g, hF⟩ := hFV
  change (∫ p, F p ∂μ.prod ν) ≤ C
  rw [hsplit F f g hF]
  apply hdual f g
  intro x y
  rw [← hF (x, y)]
  exact hle (x, y)

end NLAlib
