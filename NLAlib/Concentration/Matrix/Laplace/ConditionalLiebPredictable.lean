import NLAlib.ForMathlib.MeasureTheory.ConditionalParameterJensen
import NLAlib.Concentration.Matrix.Laplace.TraceIntegrability
import NLAlib.Concentration.Matrix.Bernstein.ConditionalCgf

/-!
# Actual conditional Lieb inequality for a predictable Hermitian offset

The self-adjoint projection bundles an almost-everywhere Hermitian predictable offset.
The proved parameter Jensen theorem then combines countably many genuine fixed-offset
Lieb inequalities. Upper bounds supply all integrability; no lower bounds are required.
-/

noncomputable section

open MeasureTheory Matrix Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

/-- Conditional Lieb with an actual conditioning-measurable Hermitian random offset.
The underlying probability space is arbitrary. Upper-only spectral bounds derive every
integrability premise; positivity of the actual conditional exponential mean is the
explicit remaining prerequisite, supplied by conditional centering in the martingale use.
Source: Tropp 2011, Freedman's inequality; operator rederivations `eq:condlieb`.
atlas: matrix-freedman (partial) -/
theorem condExp_traceExp_add_le_traceExp_add_matrixLog_of_predictable
    {Ω n : Type*} {m mΩ : MeasurableSpace Ω} [Fintype n] [DecidableEq n] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {H X : Ω → Matrix n n ℂ} (hHMeas : Measurable[m] H) (hXMeas : Measurable X)
    (hH : ∀ᵐ ω ∂μ, (H ω).IsHermitian) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {h a : ℝ} (hHBound : ∀ᵐ ω ∂μ, H ω ≤ algebraMap ℝ (Matrix n n ℂ) h)
    (hXBound : ∀ᵐ ω ∂μ, X ω ≤ algebraMap ℝ (Matrix n n ℂ) a)
    (hmean : ∀ᵐ ω ∂μ, (μ[(fun ω => matrixExp (X ω)) | m] ω).PosDef) :
    μ[(fun ω => traceExp (H ω + X ω)) | m] ≤ᵐ[μ]
      fun ω => traceExp (H ω + matrixLog (μ[(fun ω => matrixExp (X ω)) | m] ω)) := by
  let U : Ω → selfAdjoint (Matrix n n ℂ) := fun ω => selfAdjointPart ℝ (H ω)
  let g : selfAdjoint (Matrix n n ℂ) → Matrix n n ℂ → ℝ :=
    fun p A => traceExp ((p : Matrix n n ℂ) + matrixLog A)
  have hUH : ∀ᵐ ω ∂μ, (U ω : Matrix n n ℂ) = H ω :=
    hH.mono fun ω hω => hω.isSelfAdjoint.coe_selfAdjointPart_apply ℝ
  have hUMeas : Measurable[m] U :=
    (selfAdjointPart ℝ : Matrix n n ℂ →ₗ[ℝ] selfAdjoint (Matrix n n ℂ)).continuous_of_finiteDimensional.measurable.comp hHMeas
  have hExp : Integrable (fun ω => matrixExp (X ω)) μ := by
    simpa only [one_smul] using integrable_matrixExp_smul_of_ae_le_algebraMap
      hXMeas.aestronglyMeasurable hX (show (0 : ℝ) ≤ 1 by norm_num) hXBound
  have hTrace := integrable_traceExp_add_of_ae_le_algebraMap
    (hHMeas.mono hm le_rfl).aestronglyMeasurable hXMeas.aestronglyMeasurable hH hX hHBound hXBound
  have hfixed : ∀ p : selfAdjoint (Matrix n n ℂ), Integrable (fun ω => g p (matrixExp (X ω))) μ := by
    intro p
    have hi := integrable_traceExp_add_of_ae_le_algebraMap
      (H := fun _ => (p : Matrix n n ℂ)) aestronglyMeasurable_const hXMeas.aestronglyMeasurable
      (ae_of_all μ fun _ => p.property) hX
      (ae_of_all μ fun _ => p.property.le_algebraMap_norm_self) hXBound
    apply hi.congr
    filter_upwards [hX] with ω hω
    dsimp [g]
    rw [(posDef_matrixExp_and_matrixLog_matrixExp_finite _ hω).2]
  have heq : (fun ω => g (U ω) (matrixExp (X ω))) =ᵐ[μ]
      (fun ω => traceExp (H ω + X ω)) := by
    filter_upwards [hUH, hX] with ω hUω hXω
    dsimp [g]
    rw [hUω, (posDef_matrixExp_and_matrixLog_matrixExp_finite _ hXω).2]
  have hcomp : ∀ p q : selfAdjoint (Matrix n n ℂ), ∀ A ∈ {A : Matrix n n ℂ | A.PosDef},
      ∀ δ : ℝ, 0 ≤ δ → dist p q ≤ δ → g p A ≤ Real.exp δ * g q A := by
    intro p q A hA δ hδ hd
    have hl : (matrixLog A).IsHermitian := cfc_predicate Real.log A
    apply traceExp_le_exp_mul_traceExp_of_norm_sub_le _ _ (p.property.add hl) (q.property.add hl)
    have hh : dist (p : Matrix n n ℂ) (q : Matrix n n ℂ) ≤ δ := hd
    rw [dist_eq_norm] at hh
    simpa only [add_sub_add_right_eq_sub] using hh
  have hpos : ∀ᵐ ω ∂μ, (matrixExp (X ω)).PosDef :=
    hX.mono fun ω hω => (posDef_matrixExp_and_matrixLog_matrixExp_finite _ hω).1
  have hJ := condExp_family_le_family_condExp_of_exponential_comparison hm
    (g := g) (f := fun ω => matrixExp (X ω)) (U := U)
    (fun p => lieb_concavity_finite (p : Matrix n n ℂ) p.property)
    (fun p => continuousOn_traceExp_add_matrixLog_finite (p : Matrix n n ℂ))
    hcomp hpos hExp hfixed (hTrace.congr heq.symm) hmean hUMeas
  filter_upwards [hJ, condExp_congr_ae heq, hUH] with ω hJω hEqω hUω
  change μ[(fun ω => g (U ω) (matrixExp (X ω))) | m] ω ≤
    traceExp ((U ω : Matrix n n ℂ) + matrixLog (μ[(fun ω => matrixExp (X ω)) | m] ω)) at hJω
  rw [hEqω, hUω] at hJω
  exact hJω

end NLAlib
