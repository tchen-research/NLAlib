import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Analysis.Matrix.Normed
import NLAlib.Probability.Exchangeable.Bilinear
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Trace and full coordinate covariance of an exchangeable matrix pair

These identities use actual equality of the swapped joint laws and conditional
expectation on the original matrix. They hold for all complex matrices, hence
in particular for the Hermitian matrices in Tropp's §6.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix
namespace NLAlib

private def finiteBilinCLM {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] G) : E →L[ℝ] F →L[ℝ] G :=
  ((LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] G) ≃ₗ[ℝ] (F →L[ℝ] G)).toLinearMap.comp B).toContinuousLinearMap

variable {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Trace integration by parts for a square-integrable complex exchangeable
matrix pair. Ordinary trace is used; scaling both sides gives the normalized
trace variant. Source: Tropp (2026), §6.3, equation (6.3); atlas
`exchangeable-matrix-covariance`.
atlas: exchangeable-matrix-covariance (partial) -/
theorem integral_trace_mul_exchangeable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X X' : Ω → Matrix n n ℂ}
    (hex : IdentDistrib (fun ω => (X ω, X' ω)) (fun ω => (X' ω, X ω)) μ μ)
    (hXm : Measurable X) (hX : MemLp X 2 μ)
    (f : Matrix n n ℂ → Matrix n n ℂ) (hf : Measurable f)
    (hfX : MemLp (f ∘ X) 2 μ) (α : ℝ) (hα : α ≠ 0)
    (hreg : μ[X - X' | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω => α • (X ω - ∫ t, X t ∂μ)) :
    (∫ ω, ((X ω - ∫ t, X t ∂μ) * f (X ω)).trace ∂μ) =
      (2 * α)⁻¹ • ∫ ω, ((X ω - X' ω) * (f (X ω) - f (X' ω))).trace ∂μ := by
  classical
  let B : Matrix n n ℂ →L[ℝ] Matrix n n ℂ →L[ℝ] ℂ :=
    finiteBilinCLM ((mulLinearMap ℝ).compr₂ (traceLinearMap n ℝ ℂ))
  have hm : MeasurableSpace.comap X inferInstance ≤ ‹MeasurableSpace Ω› := hXm.comap_le
  have hx : @Measurable Ω (Matrix n n ℂ) (MeasurableSpace.comap X inferInstance) _ X :=
    measurable_iff_comap_le.mpr le_rfl
  have hfm : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] (f ∘ X) μ :=
    (hf.comp hx).stronglyMeasurable.aestronglyMeasurable
  exact integral_bilin_exchangeable hex hX f hf hfX hm hfm α hα hreg B

open scoped Matrix.Norms.L2Operator in
/-- The unstarred Kronecker covariance identity of an exchangeable matrix pair.
For Hermitian matrices, these entry products also determine all conjugated
entry covariances. Source: Tropp (2026), §6.3; atlas
`exchangeable-matrix-covariance`.
atlas: exchangeable-matrix-covariance (partial) -/
theorem integral_kronecker_exchangeable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X X' : Ω → Matrix n n ℂ}
    (hex : IdentDistrib (fun ω => (X ω, X' ω)) (fun ω => (X' ω, X ω)) μ μ)
    (hXm : Measurable X) (hX : MemLp X 2 μ)
    (α : ℝ) (hα : α ≠ 0)
    (hreg : μ[X - X' | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω => α • (X ω - ∫ t, X t ∂μ)) :
    (∫ ω, Matrix.kronecker (X ω - ∫ t, X t ∂μ) (X ω - ∫ t, X t ∂μ) ∂μ) =
      (2 * α)⁻¹ • ∫ ω, Matrix.kronecker (X ω - X' ω) (X ω - X' ω) ∂μ := by
  classical
  let B : Matrix n n ℂ →L[ℝ] Matrix n n ℂ →L[ℝ] Matrix (n × n) (n × n) ℂ :=
    finiteBilinCLM (Matrix.kroneckerBilinear : Matrix n n ℂ →ₗ[ℝ]
      Matrix n n ℂ →ₗ[ℝ] Matrix (n × n) (n × n) ℂ)
  let f : Matrix n n ℂ → Matrix n n ℂ := fun A => A - ∫ t, X t ∂μ
  have hf : Measurable f := measurable_id.sub measurable_const
  have hfX : MemLp (f ∘ X) 2 μ := hX.sub (memLp_const _)
  have hm : MeasurableSpace.comap X inferInstance ≤ ‹MeasurableSpace Ω› := hXm.comap_le
  have hx : @Measurable Ω (Matrix n n ℂ) (MeasurableSpace.comap X inferInstance) _ X :=
    measurable_iff_comap_le.mpr le_rfl
  have hfm : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] (f ∘ X) μ :=
    (hf.comp hx).stronglyMeasurable.aestronglyMeasurable
  have h := integral_bilin_exchangeable hex hX f hf hfX hm hfm α hα hreg B
  change (∫ ω, Matrix.kronecker (X ω - ∫ t, X t ∂μ) (X ω - ∫ t, X t ∂μ) ∂μ) =
    (2 * α)⁻¹ • ∫ ω, Matrix.kronecker (X ω - X' ω)
      ((X ω - ∫ t, X t ∂μ) - (X' ω - ∫ t, X t ∂μ)) ∂μ at h
  simpa only [sub_sub_sub_cancel_right] using h

open scoped Matrix.Norms.L2Operator in
/-- The complete real-coordinate covariance tensor identity, in any finite
real coordinate system `r` on complex matrices. Choosing all real and imaginary
entry coordinates retains every covariance, rather than only `E[(X-EX)^2]`.
Source: Tropp (2026), §6.3; atlas `exchangeable-matrix-covariance`.
atlas: exchangeable-matrix-covariance (partial) -/
theorem integral_real_covariance_tensor_exchangeable
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X X' : Ω → Matrix n n ℂ}
    (hex : IdentDistrib (fun ω => (X ω, X' ω)) (fun ω => (X' ω, X ω)) μ μ)
    (hXm : Measurable X) (hX : MemLp X 2 μ)
    (α : ℝ) (hα : α ≠ 0)
    (hreg : μ[X - X' | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω => α • (X ω - ∫ t, X t ∂μ))
    (r : Matrix n n ℂ →L[ℝ] (κ → ℝ)) :
    (∫ ω, Matrix.vecMulVec (r (X ω - ∫ t, X t ∂μ))
      (r (X ω - ∫ t, X t ∂μ)) ∂μ) =
      (2 * α)⁻¹ • ∫ ω, Matrix.vecMulVec (r (X ω - X' ω)) (r (X ω - X' ω)) ∂μ := by
  classical
  let B : Matrix n n ℂ →L[ℝ] Matrix n n ℂ →L[ℝ] Matrix κ κ ℝ :=
    finiteBilinCLM ((vecMulVecBilin ℝ ℝ).compl₁₂ r.toLinearMap r.toLinearMap)
  let f : Matrix n n ℂ → Matrix n n ℂ := fun A => A - ∫ t, X t ∂μ
  have hf : Measurable f := measurable_id.sub measurable_const
  have hfX : MemLp (f ∘ X) 2 μ := hX.sub (memLp_const _)
  have hm : MeasurableSpace.comap X inferInstance ≤ ‹MeasurableSpace Ω› := hXm.comap_le
  have hx : @Measurable Ω (Matrix n n ℂ) (MeasurableSpace.comap X inferInstance) _ X :=
    measurable_iff_comap_le.mpr le_rfl
  have hfm : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] (f ∘ X) μ :=
    (hf.comp hx).stronglyMeasurable.aestronglyMeasurable
  have h := integral_bilin_exchangeable hex hX f hf hfX hm hfm α hα hreg B
  change (∫ ω, Matrix.vecMulVec (r (X ω - ∫ t, X t ∂μ))
    (r (X ω - ∫ t, X t ∂μ)) ∂μ) =
    (2 * α)⁻¹ • ∫ ω, Matrix.vecMulVec (r (X ω - X' ω))
      (r ((X ω - ∫ t, X t ∂μ) - (X' ω - ∫ t, X t ∂μ))) ∂μ at h
  simpa only [sub_sub_sub_cancel_right] using h

end NLAlib
