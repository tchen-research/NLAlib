import NLAlib.Matrix.Functions.KTransformStieltjesLaw
import NLAlib.Matrix.Functions.KTransformExteriorImaginary
import NLAlib.Matrix.Norms.TraceImaginary

/-! # The actual compact Stieltjes probability law of the nonlinear K branch

Compact support follows from the proved native exterior imaginary
estimate and positive Stieltjes inversion. No representing law, support
bound, branch, or normalization is supplied to the final theorem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- The actual compact Hermitian sample law constructs a global
analytic native K branch and its unique compactly supported Stieltjes
probability law. Native positivity, normalization, and compact support
are all proved from the original nonlinear equation. No branch, law,
support, or normalization conclusion appears as a premise.
Source: Montanari--Saeed (2026), Proposition 1, equations (9)--(10), and Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_analytic_matrixKTransform_compact_stieltjes_probability_measure
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) :
    ∃ F : ℂ → M, AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} ∧
      (∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
        matrixKTransform ν α (F z)=z•1) ∧
      ∃! μ : FiniteMeasure ℝ, μ.mass=1 ∧ IsCompact (μ : Measure ℝ).support ∧
        ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
          ∫ x : ℝ, ((x : ℂ)-z)⁻¹ ∂(μ : Measure ℝ) := by
  obtain ⟨F,hFa,hF,μ,hμ,huniq⟩ :=
    exists_analytic_matrixKTransform_stieltjes_probability_measure ν hν α hα
  obtain ⟨R0,hR0⟩ := hν.isBounded.exists_norm_le
  let R := max R0 1
  have hR : 0<R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ T ∈ ν.support, specNorm T.val≤R := by
    intro T hT
    have hTN : specNorm T.val≤R0 := by
      simpa only [specNorm_eq_norm,← AddSubgroup.norm_coe] using hR0 T hT
    exact hTN.trans (le_max_left _ _)
  let κ := 4*(α+1)*R/α
  let C := 2*α^2*(((α+1)*R)⁻¹)^2
  have hsupp : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x∈Icc (-κ) κ := by
    apply ae_mem_Icc_of_im_cauchyKernel_le_mul (μ : Measure ℝ) κ
    intro a ha
    refine ⟨C,?_⟩
    intro z hz hza
    have ha' : 4*(α+1)*R<a*α := (div_lt_iff₀ hα).mp ha
    have hfar : 4*(α+1)*R<α*|z.re| := by
      nlinarith [mul_le_mul_of_nonneg_left hza hα.le]
    rw [← hμ.2 z hz]
    have htrace : (normalizedTrace (α•F z)).im≤‖(imaginaryPart (α•F z) : M)‖ := by
      simpa only [specNorm_eq_norm] using im_normalizedTrace_le_specNorm_imaginaryPart (α•F z)
    exact htrace.trans
      (norm_imaginaryPart_matrixKTransform_solution_le_exterior ν hν α R hα hR F
        hFa hF hbound z hz hfar)
  have hcompact : IsCompact (μ : Measure ℝ).support :=
    isCompact_Icc.of_isClosed_subset (μ : Measure ℝ).isClosed_support
      ((μ : Measure ℝ).support_subset_of_isClosed isClosed_Icc hsupp)
  refine ⟨F,hFa,hF,μ,⟨hμ.1,hcompact,hμ.2⟩,?_⟩
  intro σ hσ
  exact huniq σ ⟨hσ.1,hσ.2.2⟩

end NLAlib
