import NLAlib.Concentration.Matrix.Martingale.LocalSecondMoment
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Predictable cuts preserve actual centering and extended local moments

The localized increments and variance use the same actual conditioning-measurable cut.
Their extended quadratic moment identities are inherited on intersections of sets.
-/

noncomputable section

open MeasureTheory Matrix Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {Ω n : Type*} {m mΩ : MeasurableSpace Ω} [Fintype n] {μ : Measure Ω}

/-- Predictable indicator localization preserves the full extended local second-moment
interface, with no integrability assumption on the original square or variance.
Source: supplied audit `audit:combined`; atlas `matrix-freedman` (partial). -/
theorem HasLocalMatrixSecondMoment.indicator {X V : Ω → Matrix n n ℂ}
    (h : HasLocalMatrixSecondMoment μ m X V) (hm : m ≤ mΩ)
    {C : Set Ω} (hC : MeasurableSet[m] C) :
    HasLocalMatrixSecondMoment μ m (C.indicator X) (C.indicator V) := by
  refine ⟨h.measurable.indicator hC, ?_, ?_⟩
  · filter_upwards [h.ae_posSemidef] with ω hω
    by_cases hωC : ω ∈ C
    · simpa only [Set.indicator_of_mem hωC] using hω
    · simpa only [Set.indicator_of_notMem hωC] using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  · intro u B hB
    have hXfun : (fun ω => ENNReal.ofReal (matrixVectorSqNorm (C.indicator X ω) u)) =
        C.indicator (fun ω => ENNReal.ofReal (matrixVectorSqNorm (X ω) u)) := by
      funext ω
      by_cases hωC : ω ∈ C
      · simp only [Set.indicator_of_mem hωC]
      · simp only [Set.indicator_of_notMem hωC, matrixVectorSqNorm, Matrix.zero_mulVec,
          Pi.zero_apply, norm_zero, zero_pow two_ne_zero, Finset.sum_const_zero, ENNReal.ofReal_zero]
    have hVfun : (fun ω => ENNReal.ofReal (matrixQuadraticFormReal (C.indicator V ω) u)) =
        C.indicator (fun ω => ENNReal.ofReal (matrixQuadraticFormReal (V ω) u)) := by
      funext ω
      by_cases hωC : ω ∈ C
      · simp only [Set.indicator_of_mem hωC]
      · simp only [Set.indicator_of_notMem hωC, matrixQuadraticFormReal, Matrix.zero_mulVec,
          dotProduct_zero, Complex.zero_re, ENNReal.ofReal_zero]
    rw [hXfun, hVfun, lintegral_indicator (hm _ hC), lintegral_indicator (hm _ hC),
      Measure.restrict_restrict (hm _ hC)]
    exact h.setLIntegral_eq u (C ∩ B) (hC.inter hB)

/-- Predictable localization of an integrable centered matrix remains integrable and
actually conditionally centered, by the conditional indicator pull-out identity.
Source: supplied audit `audit:combined`; atlas `matrix-freedman` (partial). -/
theorem integrable_indicator_and_condExp_indicator_eq_zero [DecidableEq n]
    {X : Ω → Matrix n n ℂ} (hm : m ≤ mΩ) (hX : Integrable X μ)
    (hMean : μ[X | m] =ᵐ[μ] 0) {C : Set Ω} (hC : MeasurableSet[m] C) :
    Integrable (C.indicator X) μ ∧ μ[C.indicator X | m] =ᵐ[μ] 0 := by
  refine ⟨hX.indicator (hm _ hC), ?_⟩
  filter_upwards [condExp_indicator hX hC, hMean] with ω hEq hzero
  rw [hEq]
  by_cases hωC : ω ∈ C
  · simpa only [Set.indicator_of_mem hωC] using hzero
  · simp only [Set.indicator_of_notMem hωC, Pi.zero_apply]

end NLAlib
