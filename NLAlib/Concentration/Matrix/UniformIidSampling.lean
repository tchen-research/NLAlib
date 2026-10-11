import NLAlib.ForMathlib.Probability.UniformProduct
import NLAlib.Concentration.Matrix.SamplingSpectralBounds

/-!
# Chernoff for the actual uniform iid finite population law

Independence and the expectations are derived from the literal uniform
sequence distribution. Supports the with-replacement `sh:srht-ose` variant.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Classical Matrix Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

/-- The actual iid uniform empirical mean satisfies the two-sided operator
norm Chernoff bound. Source: `sh:srht-ose`, with-replacement variant. -/
theorem measure_spectralNorm_uniform_iid_sub_one_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {d k : ℕ} [NeZero d]
    (hk : 0 < k) (A : α → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hA : ∀ j, (A j).IsHermitian)
    (hbound : ∀ j, 0 ≤ lambdaMin (A j) ∧ lambdaMax (A j) ≤ L)
    (hmean : (1 / (Fintype.card α : ℝ)) • ∑ j, A j = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ((PMF.uniformOfFintype (Fin k → α)).toMeasure
      {I | ε ≤ spectralNorm ((1 / (k : ℝ)) • ∑ a, A (I a) - 1)}).toReal ≤
      2 * d * Real.exp (-(ε ^ 2) * k / (3 * L)) := by
  let μ := (PMF.uniformOfFintype (Fin k → α)).toMeasure
  let X : Fin k → (Fin k → α) → Matrix (Fin d) (Fin d) ℂ := fun a I => A (I a)
  have hm (a : Fin k) : Measurable (X a) := Measurable.of_discrete
  have hi : iIndepFun X μ := iIndepFun_uniform_sequence_comp (ι := Fin k) A
  have hh (a : Fin k) : ∀ᵐ I ∂μ, (X a I).IsHermitian :=
    Filter.Eventually.of_forall (fun I => hA (I a))
  have hb (a : Fin k) : ∀ᵐ I ∂μ, 0 ≤ lambdaMin (X a I) ∧ lambdaMax (X a I) ≤ L :=
    Filter.Eventually.of_forall (fun I => hbound (I a))
  have he (a : Fin k) : ∫ I, X a I ∂μ = 1 := by
    change (∫ I : Fin k → α, A (I a) ∂(PMF.uniformOfFintype (Fin k → α)).toMeasure) = 1
    rw [integral_uniform_sequence_comp_eval A a]
    exact hmean
  obtain ⟨hl, hu⟩ := matrix_chernoff_sampling μ hk X L hL hm hi hh hb he hε.le hε1
  let Y : (Fin k → α) → Matrix (Fin d) (Fin d) ℂ :=
    fun I => (1 / (k : ℝ)) • ∑ a, A (I a)
  have hsub : {I | ε ≤ spectralNorm (Y I - 1)} ⊆
      {I | lambdaMin (Y I) ≤ 1 - ε} ∪ {I | 1 + ε ≤ lambdaMax (Y I)} := by
    intro I hI
    have hs : (∑ a, A (I a)).IsHermitian := isSelfAdjoint_sum _ (fun a _ => hA (I a))
    have hY : (Y I).IsHermitian := hs.smul (IsSelfAdjoint.all (1 / (k : ℝ)))
    exact lambdaMin_le_or_le_lambdaMax_of_le_spectralNorm_sub_one hY hI
  have he' : d * Real.exp (-(ε ^ 2) * k / (2 * L)) ≤
      d * Real.exp (-(ε ^ 2) * k / (3 * L)) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ ε ^ 2 * (k : ℝ) := by positivity
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * L) (by positivity : 0 < 3 * L)]
    nlinarith
  calc
    _ ≤ (μ ({I | lambdaMin (Y I) ≤ 1 - ε} ∪ {I | 1 + ε ≤ lambdaMax (Y I)})).toReal :=
      measureReal_mono hsub
    _ ≤ (μ {I | lambdaMin (Y I) ≤ 1 - ε}).toReal +
        (μ {I | 1 + ε ≤ lambdaMax (Y I)}).toReal := measureReal_union_le _ _
    _ ≤ d * Real.exp (-(ε ^ 2) * k / (2 * L)) +
        d * Real.exp (-(ε ^ 2) * k / (3 * L)) := add_le_add hl hu
    _ ≤ _ := by linarith

end NLAlib
