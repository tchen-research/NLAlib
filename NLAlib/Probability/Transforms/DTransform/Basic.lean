import NLAlib.ForMathlib.MeasureTheory.IntervalSupport
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Singular-value D-transforms

The actual compact-support integral transforms used to select a singular-value
threshold. The logarithmic derivative is defined using the ordinary derivative
of the product transform. Source: Donoho--Gavish--Romanov, ScreeNOT, Lemma 8.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace NLAlib

/-- Inverse-denominator moments of a singular-value law. -/
def dTransformMoment (μ : Measure ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  ∫ z, ((y ^ 2 - z ^ 2)⁻¹) ^ (k + 1) ∂μ

/-- The singular-value Cauchy transform, evaluated above the support. -/
def singularValuePhi (μ : Measure ℝ) (y : ℝ) : ℝ :=
  ∫ z, y / (y ^ 2 - z ^ 2) ∂μ

/-- The rectangular companion singular-value transform. -/
def singularValueCompanionPhi (μ : Measure ℝ) (γ y : ℝ) : ℝ :=
  γ * singularValuePhi μ y + (1 - γ) / y

/-- The singular-value D-transform is the product of the original and
rectangular companion transforms. -/
def singularValueDTransform (μ : Measure ℝ) (γ y : ℝ) : ℝ :=
  singularValuePhi μ y * singularValueCompanionPhi μ γ y

/-- Logarithmic elasticity of the singular-value Cauchy transform. -/
def singularValueElasticity (μ : Measure ℝ) (y : ℝ) : ℝ :=
  y * deriv (singularValuePhi μ) y / singularValuePhi μ y

/-- The native logarithmic derivative used by the ScreeNOT root equation. -/
def singularValuePsi (μ : Measure ℝ) (γ y : ℝ) : ℝ :=
  y * deriv (singularValueDTransform μ γ) y / singularValueDTransform μ γ y

/-- Mixing a singular-value law with an atom at zero realizes its rectangular
companion transform as another actual probability law when `0 ≤ γ ≤ 1`. -/
def dTransformCompanionMeasure (μ : Measure ℝ) (γ : ℝ) : Measure ℝ :=
  ENNReal.ofReal γ • μ + ENNReal.ofReal (1 - γ) • Measure.dirac 0

/-- The singular-value transform is the first inverse-denominator moment
multiplied by the evaluation point. -/
theorem singularValuePhi_eq_mul_moment (μ : Measure ℝ) (y : ℝ) :
    singularValuePhi μ y = y * dTransformMoment μ 0 y := by
  simp only [singularValuePhi, dTransformMoment, zero_add, pow_one, div_eq_mul_inv,
    integral_const_mul]

/-- The denominator is strictly positive above a nonnegative support bound. -/
theorem dTransform_denominator_pos {b y z : ℝ} (hb : 0 ≤ b) (hy : b < y)
    (hz : z ∈ Icc 0 b) : 0 < y ^ 2 - z ^ 2 := by
  have hy0 : 0 ≤ y := le_trans hb hy.le
  exact sub_pos.mpr ((sq_lt_sq₀ hz.1 hy0).mpr (lt_of_le_of_lt hz.2 hy))

/-- Every inverse-denominator moment is integrable above the compact support. -/
theorem integrable_dTransformMoment_kernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b y : ℝ} (hb : 0 ≤ b) (hsupport : μ.support ⊆ Icc 0 b) (hy : b < y) (k : ℕ) :
    Integrable (fun z => ((y ^ 2 - z ^ 2)⁻¹) ^ (k + 1)) μ := by
  have hden (z : ℝ) (hz : z ∈ μ.support) : y ^ 2 - z ^ 2 ≠ 0 :=
    (dTransform_denominator_pos hb hy (hsupport hz)).ne'
  have hc : ContinuousOn (fun z : ℝ => ((y ^ 2 - z ^ 2)⁻¹) ^ (k + 1)) μ.support :=
    ((continuousOn_const.sub (continuousOn_id.pow 2)).inv₀ hden).pow (k + 1)
  have hi := hc.integrableOn_compact (μ := μ) (μ.isCompact_support_of_subset_Icc hsupport)
  have hre : μ.restrict μ.support = μ :=
    Measure.restrict_eq_self_of_ae_mem (s := μ.support) μ.support_mem_ae
  rwa [IntegrableOn, hre] at hi

end NLAlib
