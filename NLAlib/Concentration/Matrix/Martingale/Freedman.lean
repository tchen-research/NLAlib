import NLAlib.Concentration.Matrix.Martingale.FreedmanGlobal
import NLAlib.Concentration.Matrix.Martingale.VarianceBudget
import NLAlib.Concentration.Matrix.Martingale.LocalSecondMomentIntegral

/-!
# Matrix Freedman with genuine finite local conditional variance

The variance interface uses nonnegative extended set integrals on every predictable
set and deterministic complex vector. A predictable finite-budget cut derives global
square integrability and the actual Bochner covariance needed by the trace process.
The original crossing is retained without a limit or a loss in the constant.
-/

noncomputable section

open MeasureTheory Matrix Finset Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

/-- The arbitrary-time upper matrix Freedman inequality on an arbitrary probability
space. Increments are adapted integrable Hermitian matrices, actually conditionally
centered, and bounded only above by `L I`. Predictable finite PSD variance increments
satisfy the genuine extended local quadratic moment identities on every predictable
set and every deterministic complex vector. Neither unconditional square integrability
nor integrability of the original variance is assumed. The bound includes `t=0` and
`L=0` and has the exact Bernstein coefficient.
Source: Tropp 2011, Theorem 1.2; supplied operator rederivations `thm:freedman` and
Part VII audit `audit:local-moment`, `audit:combined`.
atlas: matrix-freedman -/
theorem matrix_freedman
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {X V : ℕ → Ω → Matrix n n ℂ}
    (hXMeas : ∀ j, Measurable[ℱ (j + 1)] (X j))
    (hXInt : ∀ j, Integrable (X j) μ)
    (hXHerm : ∀ j, ∀ᵐ ω ∂μ, (X j ω).IsHermitian)
    (hMean : ∀ j, μ[X j | ℱ j] =ᵐ[μ] 0)
    (hLocal : ∀ j, HasLocalMatrixSecondMoment μ (ℱ j) (X j) (V j))
    {L t v : ℝ} (hL : 0 ≤ L) (ht : 0 ≤ t) (hv : 0 < v)
    (hBound : ∀ j, ∀ᵐ ω ∂μ, X j ω ≤ algebraMap ℝ (Matrix n n ℂ) L) :
    (μ {ω | ∃ k, t ≤ lambdaMax (matrixIncrementSum X k ω) ∧
        ‖matrixIncrementSum V k ω‖ ≤ v}).toReal ≤
      Fintype.card n * Real.exp (-(t ^ 2 / (2 * (v + L * t / 3)))) := by
  by_cases htp : 0 < t
  · obtain ⟨θ, hθ, hθL, hopt⟩ := exists_pos_mul_lt_three_bernstein_exponent_eq htp hv hL
    let C : ℕ → Set Ω := matrixVarianceBudgetSet V v
    let X' : ℕ → Ω → Matrix n n ℂ := fun j => (C j).indicator (X j)
    let V' : ℕ → Ω → Matrix n n ℂ := fun j => (C j).indicator (V j)
    have hVM : ∀ j, StronglyMeasurable[ℱ j] (V j) :=
      fun j => (hLocal j).measurable.stronglyMeasurable
    have hC : ∀ j, MeasurableSet[ℱ j] (C j) :=
      measurableSet_matrixVarianceBudgetSet hVM v
    have hXM : ∀ j, Measurable (X j) :=
      fun j => (hXMeas j).mono (ℱ.le (j + 1)) le_rfl
    have hX'M : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X' j) := by
      intro j
      exact (hXMeas j).stronglyMeasurable.indicator
        ((ℱ.mono (Nat.le_succ j)) _ (hC j))
    have hV'M : ∀ j, StronglyMeasurable[ℱ j] (V' j) :=
      fun j => (hVM j).indicator (hC j)
    have hX'I : ∀ j, Integrable (X' j) μ :=
      fun j => (hXInt j).indicator ((ℱ.le j) _ (hC j))
    have hX'Mean : ∀ j, μ[X' j | ℱ j] =ᵐ[μ] 0 :=
      fun j => (integrable_indicator_and_condExp_indicator_eq_zero
        (ℱ.le j) (hXInt j) (hMean j) (hC j)).2
    have hcutI : ∀ j, Integrable (V' j) μ ∧ Integrable (fun ω => X' j ω ^ 2) μ :=
      integrable_matrixVarianceBudget_indicator_and_sq hVM hXM hLocal hv.le
    have hX'Herm : ∀ j, ∀ᵐ ω ∂μ, (X' j ω).IsHermitian := by
      intro j
      filter_upwards [hXHerm j] with ω hω
      by_cases hωC : ω ∈ C j
      · simpa only [X', Set.indicator_of_mem hωC] using hω
      · simpa only [X', Set.indicator_of_notMem hωC] using
          (Matrix.isHermitian_zero : (0 : Matrix n n ℂ).IsHermitian)
    have hV'Actual : ∀ j, μ[(fun ω => X' j ω ^ 2) | ℱ j] =ᵐ[μ] V' j := by
      intro j
      exact ((hLocal j).indicator (ℱ.le j) (hC j)).condExp_sq_eq_of_integrable
        (ℱ.le j) (hcutI j).2 (hcutI j).1 (hX'Herm j)
    have hX'Bound : ∀ j, ∀ᵐ ω ∂μ, X' j ω ≤ algebraMap ℝ (Matrix n n ℂ) L := by
      intro j
      filter_upwards [hBound j] with ω hω
      by_cases hωC : ω ∈ C j
      · simpa only [X', Set.indicator_of_mem hωC] using hω
      · simp only [X', Set.indicator_of_notMem hωC]
        simpa only [Algebra.algebraMap_eq_smul_one] using
          (Matrix.PosSemidef.one.smul hL).nonneg
    have htail := measure_exists_matrix_crossing_le_of_condExp_sq
      hX'M hV'M hX'I (fun j => (hcutI j).2) hX'Herm hV'Actual hX'Mean hθ hθL hX'Bound
      (t := t) (v := v)
    rw [hopt] at htail
    have hAllPSD : ∀ᵐ ω ∂μ, ∀ j, (V j ω).PosSemidef :=
      ae_all_iff.mpr (fun j => (hLocal j).ae_posSemidef)
    have hinc : {ω | ∃ k, t ≤ lambdaMax (matrixIncrementSum X k ω) ∧
        ‖matrixIncrementSum V k ω‖ ≤ v} ≤ᵐ[μ]
        {ω | ∃ k, t ≤ lambdaMax (matrixIncrementSum X' k ω) ∧
        ‖matrixIncrementSum V' k ω‖ ≤ v} := by
      filter_upwards [hAllPSD] with ω hω hcross
      obtain ⟨k, htω, hvω⟩ := hcross
      have heq := matrixIncrementSum_indicator_eq_of_norm_le X V k ω hω hvω
      refine ⟨k, ?_, ?_⟩
      · change t ≤ lambdaMax
          (matrixIncrementSum (fun j => (matrixVarianceBudgetSet V v j).indicator (X j)) k ω)
        rw [heq.1]
        exact htω
      · change ‖matrixIncrementSum
          (fun j => (matrixVarianceBudgetSet V v j).indicator (V j)) k ω‖ ≤ v
        rw [heq.2]
        exact hvω
    exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hinc)).trans htail
  · have ht0 : t = 0 := by linarith
    rw [ht0]
    simp only [zero_pow two_ne_zero, zero_div, neg_zero, Real.exp_zero, mul_one]
    apply measureReal_le_one.trans
    exact_mod_cast Fintype.card_pos (α := n)

end NLAlib
