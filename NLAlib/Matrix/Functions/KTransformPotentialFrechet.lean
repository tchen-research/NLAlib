import NLAlib.Matrix.Functions.KTransformLogDet
import NLAlib.ForMathlib.Analysis.Matrix.DeterminantFrechetDerivative
import NLAlib.ForMathlib.MeasureTheory.CompactSmoothIntegral

/-! # Actual Frechet gradient of the K-transform potential

The real logarithmic determinant is jointly smooth near the actual compact
support fibre. Genuine differentiation under its integral gives a Frechet
derivative; the checked matrix-line identity identifies its actual gradient.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- The actual averaged determinant kernel is genuinely differentiable
in the full real matrix space. The actual compact support constructs
the local derivative bound. -/
theorem differentiableAt_integral_matrixKLogDetKernel
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (S : M) (hS : S.PosDef) (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) :
    DifferentiableAt ℝ (fun X : M => ∫ T : selfAdjoint M, matrixKLogDetKernel X T.val ∂ν) S := by
  have hval : ContDiff ℝ 1 (fun T : selfAdjoint M => (T : M)) :=
    (selfAdjoint.submodule ℝ M).subtypeL.contDiff
  have hA : ContDiff ℝ 1 (fun p : M × selfAdjoint M => 1 + p.2.val * p.1) :=
    contDiff_const.add ((hval.comp contDiff_snd).mul contDiff_fst)
  have hdet : ContDiff ℝ 1 (fun p : M × selfAdjoint M => (1 + p.2.val * p.1).det.re) :=
    Complex.reCLM.contDiff.comp ((Matrix.contDiff_det 1).comp hA)
  let U : Set (M × selfAdjoint M) := {p | (1 + p.2.val * p.1).det.re ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun hdet.continuous continuous_const
  have hF : ContDiffOn ℝ 1
      (fun p : M × selfAdjoint M => Real.log (1 + p.2.val * p.1).det.re) U :=
    hdet.contDiffOn.log (fun _ hp => hp)
  have hpoint (T : selfAdjoint M) (hT : T ∈ ν.support) : (S, T) ∈ U :=
    (Complex.pos_iff.mp (det_one_add_mul_pos_of_matrixK_admissible S T.val hS (hgap T hT))).1.ne'
  exact differentiableAt_integral_of_contDiffOn_compact_support ν hν
    (fun p : M × selfAdjoint M => Real.log (1 + p.2.val * p.1).det.re) U hU hF S hpoint

/-- The genuine Frechet derivative of the source K potential is its
actual K-transform trace gradient, on the original positive sample-gap
domain. This supports chain rules along nonlinear inverse paths.
Source: Montanari--Saeed (2026), equation (49).
atlas: block-wishart-log-potential (partial) -/
theorem hasFDerivAt_matrixKPotential
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α u : ℝ) (hα : α ≠ 0) (S : M) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) :
    HasFDerivAt (matrixKPotential ν α u)
      (α • ((Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap).comp
        (ContinuousLinearMap.mul ℝ M (matrixKTransform ν α S - (u : ℂ) • 1)))) S := by
  let T : M →L[ℝ] ℝ := Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  have htrace : DifferentiableAt ℝ (fun X : M => X.trace.re) S := T.differentiableAt
  have hI := differentiableAt_integral_matrixKLogDetKernel ν hν S hS hgap
  have hdet : DifferentiableAt ℝ (fun X : M => X.det.re) S :=
    Complex.reCLM.differentiableAt.comp S ((Matrix.contDiff_det 1).differentiable one_ne_zero S)
  have hlog := hdet.log (Complex.pos_iff.mp hS.det_pos).1.ne'
  have hpot : DifferentiableAt ℝ (matrixKPotential ν α u) S := by
    convert! (((htrace.const_mul (-α * u)).add (hI.const_mul α)).sub hlog).sub_const
      ((Fintype.card n : ℝ) * (Real.log α + 1)) using 1
  have hD := hpot.hasFDerivAt
  have he : fderiv ℝ (matrixKPotential ν α u) S =
      α • ((Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap).comp
        (ContinuousLinearMap.mul ℝ M (matrixKTransform ν α S - (u : ℂ) • 1))) := by
    ext H
    change fderiv ℝ (matrixKPotential ν α u) S H =
      α * ((matrixKTransform ν α S - (u : ℂ) • 1) * H).trace.re
    have hline : HasDerivAt (fun t : ℝ => S + t • H) H 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add S
    have hDA : HasFDerivAt (matrixKPotential ν α u)
        (fderiv ℝ (matrixKPotential ν α u) S) (S + (0 : ℝ) • H) := by
      simpa only [zero_smul, add_zero] using hD
    have h₁ := hDA.comp_hasDerivAt (0 : ℝ) hline
    have h₂ := hasDerivAt_matrixKPotential_line ν hν α u hα S H hS hgap
    exact h₁.unique h₂
  rwa [he] at hD

end NLAlib
