import NLAlib.Matrix.Functions.KTransformBoundaryDefectBound
import NLAlib.Matrix.Functions.KTransformKernelInverse
import NLAlib.Matrix.Functions.PositiveSandwichBoundary
import NLAlib.Matrix.Functions.KTransformUpperBounds

/-! # Actual sample denominator units below the trace-law support

The true nonlinear equation supplies imaginary coercivity. The native
positive defect measures and real analytic matrix continuation supply
the boundary bound and linear perturbation estimate. The limiting
sample denominator is therefore a genuine unit, before any positivity
continuation argument.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- Every actual sample denominator is invertible below the true trace
support. No sample gap, PSD condition, boundary norm estimate, or real
K solution is assumed; those analytic estimates are derived from the
original positive half-plane branch and its actual trace law.
Source: Montanari--Saeed (2026), Theorem 3, real-gap converse.
atlas: block-wishart-variational-edges (partial) -/
theorem isUnit_inverse_add_below_matrixKTransform_trace_support
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1)
    (μ : FiniteMeasure ℝ)
    (hμ : ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ : Measure ℝ))
    (G : ℂ → M) (u : ℝ)
    (hu : ∀ t ∈ (μ : Measure ℝ).support, u<t)
    (hGa : AnalyticAt ℂ G (u : ℂ))
    (hGN : ∀ z : ℂ, 0<z.im → G z=α•F z)
    (hGpos : (G u).PosDef) :
    ∀ T ∈ ν.support, IsUnit ((α⁻¹•G u)⁻¹+T.val) := by
  let S : ℂ → M := fun z => α⁻¹•G z
  let Q : ℂ → M := fun z => (S z)⁻¹
  have hSpos : (S u).PosDef := hGpos.smul (inv_pos.mpr hα)
  have hSa : AnalyticAt ℂ S (u : ℂ) := hGa.const_smul (c := α⁻¹)
  have hQa : AnalyticAt ℂ Q (u : ℂ) := by
    have hh := analyticAt_inverse (𝕜 := ℂ) hSpos.isUnit.unit
    rw [hSpos.isUnit.unit_spec] at hh
    simpa only [Q,Function.comp_def,← Matrix.nonsing_inv_eq_ringInverse] using hh.comp (f := S) hSa
  have hQupper (z : ℂ) (hz : 0<z.im) : Q z=(F z)⁻¹ := by
    simp only [Q,S,hGN z hz,smul_smul,inv_mul_cancel₀ hα.ne',one_smul]
  obtain ⟨C,U,hU,hLip⟩ := hQa.hasStrictDerivAt.hasStrictFDerivAt.exists_lipschitzOnWith
  let φ : ℝ → ℂ := fun y => (u : ℂ)+(y : ℂ)*Complex.I
  have hφ : Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 (u : ℂ)) := by
    have hc : Continuous φ := by fun_prop
    simpa only [φ,Complex.ofReal_zero,zero_mul,add_zero] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  obtain ⟨B,hB,hbound⟩ := exists_uniform_matrixKResolvent_defect_bound_below_trace_support
    ν hν α hα F hFa hF μ hμ u hu
  intro T hT
  apply isUnit_add_of_bounded_inverse_sandwich_boundary
    ((S u)⁻¹) T.val (Matrix.isUnit_nonsing_inv_iff.mpr hSpos.isUnit) T.property
    (fun y => (F (φ y))⁻¹) α C B hα C.property hB
  filter_upwards [hφ.eventually hU,self_mem_nhdsWithin] with y hy hyp
  have hypos : 0<y := hyp
  have hz : 0<(φ y).im := by simpa [φ] using hypos
  have hFS := (hF (φ y) hz).1
  have hFSunit : IsUnit (F (φ y)) := Matrix.isUnit_of_posDef_imaginaryPart hFS
  have hden : IsUnit (1+F (φ y)*T.val) :=
    isUnit_matrixKDenominator_of_posDef_imaginaryPart (F (φ y)) T.val hFS T.property
  have hcoercive : (α*y)•(1 : M)≤ -(imaginaryPart ((F (φ y))⁻¹) : M) := by
    have hh := (matrixKTransform_solution_inverse_variable ν hν α hα
      ((φ y)•1) (F (φ y)) hFS (hF (φ y) hz).2).2
    have hIm : (imaginaryPart ((φ y)•(1 : M)) : M)=y•1 := by
      have hI : IsSelfAdjoint (1 : M) := IsSelfAdjoint.one _
      simp [imaginaryPart_smul,hI.imaginaryPart,realPart_one,φ]
    simpa only [map_neg,NegMemClass.coe_neg,hIm,smul_smul] using hh
  have hdist : ‖φ y-(u : ℂ)‖=y := by
    simp only [φ,add_sub_cancel_left,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,
      Real.norm_of_nonneg hypos.le]
  have hpert : ‖(F (φ y))⁻¹-(S u)⁻¹‖≤(C : ℝ)*y := by
    rw [← hQupper _ hz]
    simpa only [Q,hdist] using lipschitzOnWith_iff_norm_sub_le.mp hLip hy (mem_of_mem_nhds hU)
  refine ⟨isUnit_inverse_add_of_isUnit_matrixKDenominator _ _ hFSunit hden,
    hcoercive,hpert,?_⟩
  rw [← matrixKResolvent_defect_eq_inverse_sandwich _ _ hFSunit hden]
  exact hbound T hT (φ y) hz (by simp [φ])

end NLAlib
