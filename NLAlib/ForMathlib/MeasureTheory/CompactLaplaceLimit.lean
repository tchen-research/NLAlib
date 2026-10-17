import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Limits of compactly supported exponential representations

Positive finite measures on a common compact set with bounded mass form a compact
space. Consequently, pointwise limits of their integrals against any family of continuous
test functions have a single representing positive measure. The exponential specialization
is the compactness step used to remove simple-spectrum assumptions from Stahl's BMV
representation (Stahl 2013, Theorem 1; Eremenko's exposition). It does not assume or prove
the spectral-surface construction or positivity of Stahl's contour density.

This file provides reusable limit infrastructure for atlas `trace-exponential-stahl`.
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal

namespace NLAlib

/-- Pointwise limits of integrals against a family of continuous functions on a compact
space retain a single positive finite representing measure, provided the approximating
measures have a common mass bound. The index filter is arbitrary and nontrivial.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem exists_finiteMeasure_integral_eq_of_tendsto
    {X T I : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [BorelSpace X] [CompactSpace X] {l : Filter I} [l.NeBot]
    (K : T → C(X, ℝ)) (C : ℝ≥0) (F : I → T → ℝ) (f : T → ℝ)
    (hrep : ∀ᶠ i in l, ∃ μ : FiniteMeasure X,
      μ.mass ≤ C ∧ ∀ t, ∫ x, K t x ∂μ = F i t)
    (hlim : ∀ t, Tendsto (fun i => F i t) l (𝓝 (f t))) :
    ∃ μ : FiniteMeasure X, μ.mass ≤ C ∧ ∀ t, ∫ x, K t x ∂μ = f t := by
  let L : FiniteMeasure X → T → ℝ := fun μ t => ∫ x, K t x ∂μ
  have hL : Continuous L := continuous_pi fun t =>
    FiniteMeasure.continuous_integral_continuousMap (K t)
  have hc : IsCompact (L '' {μ : FiniteMeasure X | μ.mass ≤ C}) :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X C).image hL
  have hf : f ∈ L '' {μ : FiniteMeasure X | μ.mass ≤ C} := by
    apply hc.isClosed.mem_of_tendsto (tendsto_pi_nhds.mpr hlim)
    filter_upwards [hrep] with i hi
    obtain ⟨μ, hμ, heq⟩ := hi
    exact ⟨μ, hμ, funext heq⟩
  obtain ⟨μ, hμ, heq⟩ := hf
  exact ⟨μ, hμ, fun t => congrFun heq t⟩

/-- A pointwise limit of exponential transforms of positive finite measures on a common
compact interval is again an exponential transform on that interval, under a common mass
bound. This is the measure-compactness part of the repeated-eigenvalue reduction in Stahl's
BMV theorem; the full contour representation is a separate theorem. Empty intervals and
zero measures are included.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem exists_finiteMeasure_exp_mul_eq_of_tendsto_of_mass_le
    {I : Type*} {l : Filter I} [l.NeBot] (a b : ℝ) (C : ℝ≥0)
    (F : I → ℝ → ℝ) (f : ℝ → ℝ)
    (hrep : ∀ᶠ i in l, ∃ μ : FiniteMeasure ℝ, μ.mass ≤ C ∧
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) ∧
      ∀ t, ∫ x, Real.exp (t * x) ∂(μ : Measure ℝ) = F i t)
    (hlim : ∀ t, Tendsto (fun i => F i t) l (𝓝 (f t))) :
    ∃ μ : FiniteMeasure ℝ, μ.mass ≤ C ∧
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) ∧
      ∀ t, ∫ x, Real.exp (t * x) ∂(μ : Measure ℝ) = f t := by
  let K : ℝ → C(Icc a b, ℝ) := fun t =>
    ⟨fun x => Real.exp (t * (x : ℝ)), by fun_prop⟩
  have hrep' : ∀ᶠ i in l, ∃ μ : FiniteMeasure (Icc a b),
      μ.mass ≤ C ∧ ∀ t, ∫ x, K t x ∂μ = F i t := by
    filter_upwards [hrep] with i hi
    obtain ⟨μ, hmass, hsupp, hμ⟩ := hi
    refine ⟨μ.comap Subtype.val, (FiniteMeasure.mass_comap_le _ _).trans hmass, ?_⟩
    intro t
    change ∫ x : Icc a b, Real.exp (t * (x : ℝ))
      ∂(Measure.comap Subtype.val (μ : Measure ℝ)) = F i t
    rw [integral_subtype_comap (μ := (μ : Measure ℝ)) (s := Icc a b)
      measurableSet_Icc (fun x : ℝ => Real.exp (t * x)),
      Measure.restrict_eq_self_of_ae_mem hsupp, hμ]
  obtain ⟨μ, hmass, hμ⟩ :=
    exists_finiteMeasure_integral_eq_of_tendsto K C F f hrep' hlim
  refine ⟨μ.map Subtype.val, (FiniteMeasure.mass_map_le _ _).trans hmass, ?_, ?_⟩
  · change ∀ᵐ x ∂Measure.map (Subtype.val : Icc a b → ℝ) (μ : Measure (Icc a b)),
      x ∈ Icc a b
    exact (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
      (Eventually.of_forall fun x => x.property)
  · intro t
    change ∫ x, Real.exp (t * x)
      ∂Measure.map (Subtype.val : Icc a b → ℝ) (μ : Measure (Icc a b)) = f t
    have hval : IsClosedEmbedding (Subtype.val : Icc a b → ℝ) :=
      IsClosedEmbedding.subtypeVal isClosed_Icc
    rw [hval.integral_map
      (μ := (μ : Measure (Icc a b))) (fun x : ℝ => Real.exp (t * x))]
    exact hμ t

/-- A pointwise limit of exponential transforms of positive finite measures supported in a
common compact interval is represented by one positive finite measure on the same interval.
No separate mass bound is required: convergence at parameter zero bounds the masses. This
is the compactness reduction used to remove the simple-spectrum hypothesis from Stahl's
BMV representation (Stahl 2013, Theorem 1). The spectral-surface positivity theorem is not
an assumption or a conclusion here.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem exists_finiteMeasure_exp_mul_eq_of_tendsto
    {I : Type*} {l : Filter I} [l.NeBot] (a b : ℝ)
    (F : I → ℝ → ℝ) (f : ℝ → ℝ)
    (hrep : ∀ᶠ i in l, ∃ μ : FiniteMeasure ℝ,
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) ∧
      ∀ t, ∫ x, Real.exp (t * x) ∂(μ : Measure ℝ) = F i t)
    (hlim : ∀ t, Tendsto (fun i => F i t) l (𝓝 (f t))) :
    ∃ μ : FiniteMeasure ℝ,
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) ∧
      ∀ t, ∫ x, Real.exp (t * x) ∂(μ : Measure ℝ) = f t := by
  let C : ℝ≥0 := ⟨|f 0| + 1, by positivity⟩
  have hbound : ∀ᶠ i in l, F i 0 < (C : ℝ) :=
    (hlim 0).eventually (Iio_mem_nhds
      (lt_of_le_of_lt (le_abs_self (f 0)) (lt_add_one _)))
  have hrep' : ∀ᶠ i in l, ∃ μ : FiniteMeasure ℝ, μ.mass ≤ C ∧
      (∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc a b) ∧
      ∀ t, ∫ x, Real.exp (t * x) ∂(μ : Measure ℝ) = F i t := by
    filter_upwards [hrep, hbound] with i hi hbi
    obtain ⟨μ, hsupp, hμ⟩ := hi
    refine ⟨μ, ?_, hsupp, hμ⟩
    have hmass : (μ.mass : ℝ) = F i 0 := by
      calc
        (μ.mass : ℝ) = ∫ x : ℝ, (1 : ℝ) ∂(μ : Measure ℝ) := by
          simp only [integral_const, smul_eq_mul, mul_one]
          rfl
        _ = F i 0 := by simpa only [zero_mul, Real.exp_zero] using hμ 0
    change (μ.mass : ℝ) ≤ (C : ℝ)
    exact hmass.trans_le hbi.le
  obtain ⟨μ, -, hsupp, hμ⟩ :=
    exists_finiteMeasure_exp_mul_eq_of_tendsto_of_mass_le a b C F f hrep' hlim
  exact ⟨μ, hsupp, hμ⟩
end NLAlib
