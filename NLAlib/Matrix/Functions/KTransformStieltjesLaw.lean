import NLAlib.Matrix.Functions.KTransformUpperExistence
import NLAlib.Matrix.Functions.KTransformNormalization
import NLAlib.Matrix.Norms.TraceImaginary
import NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesCharacterization

/-! # The actual normalized trace law of the nonlinear K branch

The constructed global analytic branch, its native positive imaginary
part, and proved normalization produce a unique genuine positive
Stieltjes probability measure. No representing law is supplied.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- The normalized trace of an actual analytic K solver has a unique
positive Stieltjes probability measure. Its mass one follows from the
proved nonlinear K normalization, rather than a measure assumption.
Source: Montanari--Saeed (2026), Proposition 1, equations (9)--(10), and Lemma 1.
atlas: block-wishart-variational-edges (partial) -/
theorem existsUnique_stieltjes_probability_measure_of_matrixKTransform_solution
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im})
    (hF : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1) :
    ∃! μ : FiniteMeasure ℝ, μ.mass=1 ∧
      ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
        ∫ x : ℝ, ((x : ℂ)-z)⁻¹ ∂(μ : Measure ℝ) := by
  let N : ℂ → M := fun z => α•F z
  let L : M →L[ℂ] ℂ := (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap
  let f : ℂ → ℂ := fun z => L (N z)
  have hfa : AnalyticOnNhd ℂ f {z : ℂ | 0<z.im} := by
    intro z hz
    exact (L.analyticAt (N z)).comp ((hFa z hz).const_smul (c := α))
  have hfp : ∀ z : ℂ, 0<z.im → 0≤(f z).im := by
    intro z hz
    have hNpos : (imaginaryPart (N z) : M).PosSemidef := by
      have hp := ((hF z hz).1.smul hα).posSemidef
      simpa only [N,map_smul,selfAdjoint.val_smul] using hp
    exact im_normalizedTrace_nonneg_of_posSemidef_imaginaryPart (N z) hNpos
  have hnorm := tendsto_mul_I_smul_matrixKTransform_solution ν hν α hα F hF
  have hflim : Tendsto (fun y : ℝ => (y : ℂ)*Complex.I*f ((y : ℂ)*Complex.I))
      atTop (𝓝 (-(1 : ℝ) : ℂ)) := by
    have ht := (L.continuous.tendsto (-1)).comp hnorm
    simpa only [Function.comp_def,map_smul,smul_eq_mul,map_neg,L,
      LinearMap.coe_toContinuousLinearMap',normalizedTraceLinearMap_apply,
      normalizedTrace_one,f,N,Complex.ofReal_one] using ht
  have hμ := hfa.existsUnique_finiteMeasure_stieltjes_eq hfp 1 hflim
  simpa only [f,N,L,LinearMap.coe_toContinuousLinearMap',normalizedTraceLinearMap_apply] using hμ

/-- The actual compact Hermitian sample law constructs a global
analytic native K branch and its unique positive normalized-trace
Stieltjes probability law. No branch, representing measure, or
normalization hypothesis is supplied. Compact support of the resulting
law is a separate exterior-analytic conclusion.
Source: Montanari--Saeed (2026), Proposition 1, equations (9)--(10); Lemma 1 and Appendix A.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_analytic_matrixKTransform_stieltjes_probability_measure
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) :
    ∃ F : ℂ → M, AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} ∧
      (∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
        matrixKTransform ν α (F z)=z•1) ∧
      ∃! μ : FiniteMeasure ℝ, μ.mass=1 ∧
        ∀ z : ℂ, 0<z.im → normalizedTrace (α•F z)=
          ∫ x : ℝ, ((x : ℂ)-z)⁻¹ ∂(μ : Measure ℝ) := by
  obtain ⟨F,hFa,hF⟩ := exists_analytic_matrixKTransform_upperHalfPlane_solution ν hν α hα
  have hF0 : ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z)=z•1 := fun z hz => ⟨(hF z hz).1,(hF z hz).2.1⟩
  exact ⟨F,hFa,hF0,
    existsUnique_stieltjes_probability_measure_of_matrixKTransform_solution ν hν α hα F hFa hF0⟩

end NLAlib
