import NLAlib.ForMathlib.MeasureTheory.CompactSupportDifferentiation
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Differentiability of smooth compactly supported parameter integrals

Joint C1 regularity on an actual neighborhood of the support fibre gives
the genuine derivative under the measure integral. A derivative bound is
constructed by the compact-support differentiation theorem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace NLAlib
variable {X E Ω : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [LocallyCompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Ω] [NormedSpace ℝ Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-- A genuinely jointly C1 function near the actual compact support
fibre has a differentiable parameter integral. No differentiability or
derivative-domination certificate for the integral is assumed. -/
theorem differentiableAt_integral_of_contDiffOn_compact_support
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    (F : X × Ω → E) (U : Set (X × Ω)) (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (x₀ : X)
    (hpoint : ∀ a ∈ μ.support, (x₀, a) ∈ U) :
    DifferentiableAt ℝ (fun x => ∫ a, F (x, a) ∂μ) x₀ := by
  let D : X → Ω → X →L[ℝ] E := fun x a =>
    (fderiv ℝ F (x, a)).comp (ContinuousLinearMap.inl ℝ X Ω)
  have hD : ContinuousOn (fun p : X × Ω => D p.1 p.2) U := by
    change ContinuousOn (fun p : X × Ω =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ X Ω)) U
    exact (hF.continuousOn_fderiv_of_isOpen hU le_rfl).clm_comp continuousOn_const
  have hd (p : X × Ω) (hp : p ∈ U) :
      HasFDerivAt (fun x => F (x, p.2)) (D p.1 p.2) p.1 := by
    have hjoint := ((hF.contDiffAt (hU.mem_nhds hp)).differentiableAt one_ne_zero).hasFDerivAt
    have hpair : HasFDerivAt (fun x : X => (x, p.2))
        (ContinuousLinearMap.inl ℝ X Ω) p.1 := by
      convert (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1) using 1 <;> rfl
    exact hjoint.comp p.1 hpair
  exact (hasFDerivAt_integral_of_compact_support μ hμ
    (fun x a => F (x, a)) D U hU hF.continuousOn hD hd x₀ hpoint).differentiableAt

end NLAlib
