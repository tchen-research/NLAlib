import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.Order.Basic

/-!
# Increasing functions preserve upper-tail comparison

An elementary layer-cake interface for first-order stochastic comparison. The
two random variables may live on different spaces. No coupling construction is
needed: continuity writes every transformed upper level set as a countable
directed union of rational upper cuts.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace MeasureTheory

private theorem preimage_lt_eq_biUnion_rat {Ω : Type*} (X : Ω → ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) (hm : Monotone f) (t : ℝ) :
    {ω | t < f (X ω)} = ⋃ q : ℚ, ⋃ (_ : t < f q), {ω | (q : ℝ) < X ω} := by
  ext ω
  constructor
  · intro hω
    have hn : {x | t < f x} ∈ 𝓝 (X ω) :=
      (isOpen_lt continuous_const hf).mem_nhds hω
    obtain ⟨l, u, hxu, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
    obtain ⟨q, hlq, hqx⟩ := exists_rat_btwn hxu.1
    exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hlu ⟨hlq, hqx.trans hxu.2⟩, hqx⟩⟩
  · intro hω
    obtain ⟨q, hq⟩ := mem_iUnion.mp hω
    obtain ⟨hq, hqx⟩ := mem_iUnion.mp hq
    exact hq.trans_le (hm hqx.le)

private theorem directedOn_upperCuts {Ω : Type*} (X : Ω → ℝ)
    (f : ℝ → ℝ) (t : ℝ) :
    DirectedOn (fun q r : ℚ => {ω | (q : ℝ) < X ω} ⊆ {ω | (r : ℝ) < X ω})
      {q : ℚ | t < f q} := by
  intro q hq r hr
  rcases le_total q r with h | h
  · refine ⟨q, hq, subset_rfl, ?_⟩
    intro ω hω
    change (q : ℝ) < X ω
    change (r : ℝ) < X ω at hω
    exact lt_of_le_of_lt (show (q : ℝ) ≤ r by exact_mod_cast h) hω
  · refine ⟨r, hr, ?_, subset_rfl⟩
    intro ω hω
    change (r : ℝ) < X ω
    change (q : ℝ) < X ω at hω
    exact lt_of_le_of_lt (show (r : ℝ) ≤ q by exact_mod_cast h) hω

/-- Upper-tail comparison is preserved by every continuous increasing real
function, for random variables on arbitrary measure spaces. -/
theorem measure_lt_comp_le_of_measure_lt_le {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    (X : Ω → ℝ) (Y : Ω' → ℝ)
    (hXY : ∀ t : ℝ, μ {ω | t < X ω} ≤ ν {ω | t < Y ω})
    {f : ℝ → ℝ} (hf : Continuous f) (hm : Monotone f) (t : ℝ) :
    μ {ω | t < f (X ω)} ≤ ν {ω | t < f (Y ω)} := by
  classical
  rw [preimage_lt_eq_biUnion_rat X hf hm t, preimage_lt_eq_biUnion_rat Y hf hm t]
  change μ (⋃ q ∈ {q : ℚ | t < f q}, {ω | (q : ℝ) < X ω}) ≤
    ν (⋃ q ∈ {q : ℚ | t < f q}, {ω | (q : ℝ) < Y ω})
  rw [measure_biUnion_eq_iSup (Set.to_countable _) (directedOn_upperCuts X f t),
    measure_biUnion_eq_iSup (Set.to_countable _) (directedOn_upperCuts Y f t)]
  exact iSup_le fun q => iSup_le fun hq =>
    (hXY q).trans (le_iSup_of_le q (le_iSup_of_le hq le_rfl))

/-- Continuous increasing nonnegative transforms have ordered nonnegative
expectations when all scalar upper tails are ordered. -/
theorem lintegral_comp_le_of_measure_lt_le {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (hXY : ∀ t : ℝ, μ {ω | t < X ω} ≤ ν {ω | t < Y ω})
    {f : ℝ → ℝ} (hf : Continuous f) (hm : Monotone f) (hn : ∀ x, 0 ≤ f x) :
    (∫⁻ ω, ENNReal.ofReal (f (X ω)) ∂μ) ≤
      ∫⁻ ω, ENNReal.ofReal (f (Y ω)) ∂ν := by
  rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ fun _ => hn _)
      (hf.measurable.comp_aemeasurable hX),
    lintegral_eq_lintegral_meas_lt ν (ae_of_all _ fun _ => hn _)
      (hf.measurable.comp_aemeasurable hY)]
  exact lintegral_mono fun t => measure_lt_comp_le_of_measure_lt_le X Y hXY hf hm t

end MeasureTheory
