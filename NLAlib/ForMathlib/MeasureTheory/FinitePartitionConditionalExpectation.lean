import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite-partition conditional means and their actual moments

The conditional mean on each atom is an explicit normalized Bochner
integral. The zero-mass atom convention is zero. Their finite weighted norm
power sum is exactly the moment of conditional expectation, so the usual
Bochner contraction theorem applies to these concrete finite outputs.
-/

noncomputable section

open scoped BigOperators MeasureTheory
open Set

namespace MeasureTheory

variable {Ω ι E : Type*} [MeasurableSpace Ω] [Fintype ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The explicit conditional mean on one atom of a finite measurable
partition. Atoms of zero mass have mean zero. -/
def finitePartitionMean (μ : Measure Ω) (cell : Ω → ι) (f : Ω → E) (i : ι) : E :=
  (μ.real (cell ⁻¹' {i}))⁻¹ • ∫ ω in cell ⁻¹' {i}, f ω ∂μ

/-- Integration of a scalar finite-output function is exactly its atom
weighted sum, retaining atoms of mass zero. -/
theorem integral_comp_finite_eq_sum (cell : Ω → ι) (hcell : Measurable cell) (g : ι → ℝ) :
    (∫ ω, g (cell ω) ∂μ) = ∑ i, μ.real (cell ⁻¹' {i}) * g i := by
  rw [← integral_map hcell.aemeasurable (Integrable.of_finite (f := g)).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_measureReal_apply hcell (measurableSet_singleton i), smul_eq_mul]

omit [Fintype ι] in
/-- For a finite measurable partition, a conditional expectation has an
actual finite-output representation. On every positive-mass atom its value
is the explicit normalized atom integral. -/
theorem exists_condExp_finitePartitionMean_factor
    (cell : Ω → ι) (hcell : Measurable cell) {f : Ω → E} (hf : Integrable f μ) :
    ∃ g : ι → E,
      μ[f | MeasurableSpace.comap cell ‹MeasurableSpace ι›] = g ∘ cell ∧
        ∀ i, μ.real (cell ⁻¹' {i}) ≠ 0 → finitePartitionMean μ cell f i = g i := by
  have hm : MeasurableSpace.comap cell ‹MeasurableSpace ι› ≤ ‹MeasurableSpace Ω› := hcell.comap_le
  obtain ⟨g, _, hg⟩ :=
    (stronglyMeasurable_condExp (μ := μ) (f := f)
      (m := MeasurableSpace.comap cell ‹MeasurableSpace ι›)).exists_eq_measurable_comp
  refine ⟨g, hg, ?_⟩
  intro i hi
  have hsi : MeasurableSet[MeasurableSpace.comap cell ‹MeasurableSpace ι›] (cell ⁻¹' {i}) :=
    ⟨{i}, measurableSet_singleton i, rfl⟩
  have hconst : (∫ ω in cell ⁻¹' {i},
      μ[f | MeasurableSpace.comap cell ‹MeasurableSpace ι›] ω ∂μ) =
      μ.real (cell ⁻¹' {i}) • g i := by
    rw [hg]
    calc
      _ = ∫ _ω in cell ⁻¹' {i}, g i ∂μ := by
        apply setIntegral_congr_fun (hm _ hsi)
        intro ω hω
        change g (cell ω) = g i
        rw [show cell ω = i from hω]
      _ = _ := setIntegral_const _
  have hset := setIntegral_condExp hm hf hsi
  rw [hconst] at hset
  dsimp [finitePartitionMean]
  rw [← hset, smul_smul, inv_mul_cancel₀ hi, one_smul]

/-- The finite weighted power sum of explicit atom means is exactly the
actual conditional-expectation norm moment. No atom-positivity hypothesis
is imposed; zero-mass atoms contribute zero on both sides. -/
theorem sum_mul_norm_finitePartitionMean_rpow_eq_integral_condExp
    (cell : Ω → ι) (hcell : Measurable cell) {f : Ω → E} (hf : Integrable f μ) (q : ℝ) :
    (∑ i, μ.real (cell ⁻¹' {i}) * ‖finitePartitionMean μ cell f i‖ ^ q) =
      ∫ ω, ‖μ[f | MeasurableSpace.comap cell ‹MeasurableSpace ι›] ω‖ ^ q ∂μ := by
  obtain ⟨g, hg, hmean⟩ := exists_condExp_finitePartitionMean_factor cell hcell hf
  rw [hg]
  change _ = ∫ ω, (fun i => ‖g i‖ ^ q) (cell ω) ∂μ
  rw [integral_comp_finite_eq_sum (μ := μ) cell hcell (fun i => ‖g i‖ ^ q)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : μ.real (cell ⁻¹' {i}) = 0
  · rw [hi, zero_mul, zero_mul]
  · rw [hmean i hi]

/-- The explicit finite-partition mean is a contraction of every actual
integrable norm moment of order at least one. This concrete finite-output
bound is suitable for finite weighted matrix interpolation. -/
theorem sum_mul_norm_finitePartitionMean_rpow_le_integral
    (cell : Ω → ι) (hcell : Measurable cell) {f : Ω → E} (hf : Integrable f μ)
    {q : ℝ} (hq : 1 ≤ q) (hfm : Integrable (fun ω => ‖f ω‖ ^ q) μ) :
    (∑ i, μ.real (cell ⁻¹' {i}) * ‖finitePartitionMean μ cell f i‖ ^ q) ≤
      ∫ ω, ‖f ω‖ ^ q ∂μ := by
  rw [sum_mul_norm_finitePartitionMean_rpow_eq_integral_condExp cell hcell hf]
  exact integral_norm_condExp_rpow_le hq hfm

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [IsFiniteMeasure μ] in
/-- Explicit atom means commute with every continuous real linear map.
Consequently a change to an equivalent finite-dimensional matrix norm does
not alter the underlying atom mean. -/
theorem finitePartitionMean_comp_continuousLinearMap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (cell : Ω → ι) {f : Ω → E} (hf : Integrable f μ) (T : E →L[ℝ] F) (i : ι) :
    finitePartitionMean μ cell (T ∘ f) i = T (finitePartitionMean μ cell f i) := by
  dsimp [finitePartitionMean]
  rw [T.integral_comp_comm hf.restrict, map_smul]

end MeasureTheory
