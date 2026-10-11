import NLAlib.Concentration.Matrix.Martingale.TracePotential
import NLAlib.Concentration.Matrix.Martingale.LocalSecondMomentBounded
import NLAlib.Concentration.Matrix.Martingale.LocalSecondMomentIndicator

/-!
# Predictable variance-budget localization and exact crossing preservation

The cut for increment `j` uses the variance through `j+1`, which is known at time `j`.
At any original finite-budget crossing all preceding cuts equal one.
-/

noncomputable section

open MeasureTheory Matrix Finset Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]

omit [MeasurableSpace Ω] [Fintype n] [DecidableEq n] in
/-- Cumulative sums of PSD variance increments remain PSD.
Source: finite sum of positive matrices; helper for `matrix-freedman`. -/
theorem matrixIncrementSum_posSemidef (V : ℕ → Ω → Matrix n n ℂ)
    (k : ℕ) (ω : Ω) (hV : ∀ j, (V j ω).PosSemidef) :
    (matrixIncrementSum V k ω).PosSemidef :=
  Matrix.posSemidef_sum (range k) (fun j _ => hV j)

omit [MeasurableSpace Ω] [Fintype n] [DecidableEq n] in
/-- Cumulative PSD variance sums increase in Loewner order.
Source: finite sum of positive matrices; helper for `matrix-freedman`. -/
theorem matrixIncrementSum_le_matrixIncrementSum (V : ℕ → Ω → Matrix n n ℂ)
    {a b : ℕ} (hab : a ≤ b) (ω : Ω) (hV : ∀ j, (V j ω).PosSemidef) :
    matrixIncrementSum V a ω ≤ matrixIncrementSum V b ω := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (range_mono hab)
    (fun j _ _ => (hV j).nonneg)

omit [MeasurableSpace Ω] [Fintype n] [DecidableEq n] in
/-- Each PSD variance increment is bounded by the cumulative variance including it.
Source: finite sum of positive matrices; helper for `matrix-freedman`. -/
theorem le_matrixIncrementSum_succ (V : ℕ → Ω → Matrix n n ℂ)
    (j : ℕ) (ω : Ω) (hV : ∀ i, (V i ω).PosSemidef) :
    V j ω ≤ matrixIncrementSum V (j + 1) ω :=
  Finset.single_le_sum (fun i _ => (hV i).nonneg) (mem_range.mpr (Nat.lt_succ_self j))

/-- The predictable cut for increment `j` keeps exactly the samples whose cumulative
variance including `V j` has real trace at most `card(n) v`.
Source: supplied audit `audit:combined`; helper for `matrix-freedman`. -/
def matrixVarianceBudgetSet (V : ℕ → Ω → Matrix n n ℂ) (v : ℝ) (j : ℕ) : Set Ω :=
  {ω | (matrixIncrementSum V (j + 1) ω).trace.re ≤ Fintype.card n * v}

/-- The variance-budget cut is measurable before its increment is taken.
Source: predictable variance increments; supplied audit `audit:combined`;
helper for `matrix-freedman`. -/
theorem measurableSet_matrixVarianceBudgetSet
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {V : ℕ → Ω → Matrix n n ℂ}
    (hV : ∀ j, StronglyMeasurable[ℱ j] (V j)) (v : ℝ) (j : ℕ) :
    MeasurableSet[ℱ j] (matrixVarianceBudgetSet V v j) := by
  have hW : StronglyMeasurable[ℱ j] (fun ω => matrixIncrementSum V (j + 1) ω) := by
    apply Finset.stronglyMeasurable_fun_sum (range (j + 1))
    intro i hi
    exact (hV i).mono (ℱ.mono (Nat.le_of_lt_succ (mem_range.mp hi)))
  have hT : Measurable[ℱ j] (fun ω => (matrixIncrementSum V (j + 1) ω).trace.re) := by
    exact (Complex.continuous_re.comp
      (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap.continuous).measurable.comp hW.measurable
  exact measurableSet_le hT measurable_const

/-- Localized finite local moments acquire integrable variance and actual square from
the finite trace budget. The original unlocalized variance needs no integrability.
Source: supplied audit `audit:combined`; helper for `matrix-freedman`. -/
theorem integrable_matrixVarianceBudget_indicator_and_sq
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {X V : ℕ → Ω → Matrix n n ℂ}
    (hV : ∀ j, StronglyMeasurable[ℱ j] (V j))
    (hX : ∀ j, Measurable (X j))
    (hLocal : ∀ j, HasLocalMatrixSecondMoment μ (ℱ j) (X j) (V j))
    {v : ℝ} (hv : 0 ≤ v) (j : ℕ) :
    Integrable ((matrixVarianceBudgetSet V v j).indicator (V j)) μ ∧
      Integrable (fun ω => ((matrixVarianceBudgetSet V v j).indicator (X j) ω) ^ 2) μ := by
  let C := matrixVarianceBudgetSet V v j
  have hC := measurableSet_matrixVarianceBudgetSet hV v j
  have hcut := (hLocal j).indicator (ℱ.le j) hC
  apply hcut.integrable_and_integrable_sq_of_trace_le (ℱ.le j)
    ((hX j).indicator ((ℱ.le j) _ hC))
  have hall : ∀ᵐ ω ∂μ, ∀ i, (V i ω).PosSemidef :=
    ae_all_iff.mpr (fun i => (hLocal i).ae_posSemidef)
  filter_upwards [hall] with ω hω
  by_cases hωC : ω ∈ C
  · rw [Set.indicator_of_mem hωC]
    have hle : V j ω ≤ matrixIncrementSum V (j + 1) ω :=
      Finset.single_le_sum (fun i _ => (hω i).nonneg) (mem_range.mpr (Nat.lt_succ_self j))
    exact (re_trace_le_re_trace_of_le hle).trans hωC
  · rw [Set.indicator_of_notMem hωC]
    simp only [Matrix.trace_zero, Complex.zero_re]
    exact mul_nonneg (Nat.cast_nonneg _) hv

omit [MeasurableSpace Ω] in
/-- At an original crossing with variance norm at most `v`, every earlier predictable
budget cut keeps its increment. Thus both actual partial sums agree exactly.
Source: supplied audit `audit:combined`, event inclusion with no limiting argument;
helper for `matrix-freedman`. -/
theorem matrixIncrementSum_indicator_eq_of_norm_le [Nonempty n]
    (X V : ℕ → Ω → Matrix n n ℂ) {v : ℝ}
    (k : ℕ) (ω : Ω) (hV : ∀ j, (V j ω).PosSemidef)
    (hbudget : ‖matrixIncrementSum V k ω‖ ≤ v) :
    matrixIncrementSum (fun j => (matrixVarianceBudgetSet V v j).indicator (X j)) k ω =
        matrixIncrementSum X k ω ∧
      matrixIncrementSum (fun j => (matrixVarianceBudgetSet V v j).indicator (V j)) k ω =
        matrixIncrementSum V k ω := by
  have htr : (matrixIncrementSum V k ω).trace.re ≤ Fintype.card n * v :=
    (re_trace_le_card_mul_norm_of_isHermitian _
      (matrixIncrementSum_posSemidef V k ω hV).isHermitian).trans
        (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _))
  have hkeep : ∀ j ∈ range k, ω ∈ matrixVarianceBudgetSet V v j := by
    intro j hj
    apply le_trans ?_ htr
    apply re_trace_le_re_trace_of_le
    exact matrixIncrementSum_le_matrixIncrementSum V
      (Nat.succ_le_of_lt (mem_range.mp hj)) ω hV
  constructor
  all_goals
    apply Finset.sum_congr rfl
    intro j hj
    exact Set.indicator_of_mem (hkeep j hj) _

end NLAlib
