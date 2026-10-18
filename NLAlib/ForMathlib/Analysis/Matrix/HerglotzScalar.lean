import NLAlib.ForMathlib.Analysis.Matrix.QuadraticPositiveMap
import NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesCharacterization

/-!
# Actual scalar measures for matrix Herglotz probes

Holomorphy, positive matrix imaginary part, matrix normalization at infinity,
and an exterior imaginary bound construct each scalar quadratic Stieltjes
measure. No scalar representing measure is supplied to the theorem.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The nonnegative normalization mass of a quadratic matrix probe. -/
def quadraticProbeMass (v : n → ℂ) : NNReal :=
  ⟨matrixRealQuadraticFormCLM v 1, by
    change 0 ≤ (star v ⬝ᵥ (1 *ᵥ v)).re
    rw [one_mulVec]
    exact (RCLike.nonneg_iff.mp (dotProduct_star_self_nonneg v)).1⟩

/-- Probe mass is exactly the identity quadratic form. -/
theorem ofReal_quadraticProbeMass (v : n → ℂ) :
    ((quadraticProbeMass v : ℝ) : ℂ) = matrixQuadraticFormCLM v 1 := by
  apply Complex.ext
  · rfl
  · have hI : (1 : Matrix n n ℂ).IsHermitian := isHermitian_one
    exact (hI.im_star_dotProduct_mulVec_self v).symm

/-- Matrix normalization transports through each continuous quadratic probe. -/
theorem tendsto_mul_I_matrixQuadraticFormCLM
    (M : ℂ → Matrix n n ℂ)
    (hlim : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) • M ((y : ℂ) * Complex.I))
      atTop (𝓝 (-1))) (v : n → ℂ) :
    Tendsto (fun y : ℝ => (y : ℂ) * Complex.I * matrixQuadraticFormCLM v (M ((y : ℂ) * Complex.I)))
      atTop (𝓝 (-(quadraticProbeMass v : ℝ) : ℂ)) := by
  have h := ((matrixQuadraticFormCLM v).continuous.tendsto (-1)).comp hlim
  simpa only [Function.comp_def, map_smul, smul_eq_mul, map_neg,
    ← ofReal_quadraticProbeMass, Complex.ofReal_neg] using h

/-- Matrix exterior imaginary bounds transport to scalar probes with
the exact same exterior radius. -/
theorem im_matrixQuadraticFormCLM_le_mul_of_norm
    (M : ℂ → Matrix n n ℂ) (v : n → ℂ) (a C : ℝ)
    (hb : ∀ z : ℂ, 0 < z.im → a ≤ |z.re| →
      ‖(imaginaryPart (M z) : Matrix n n ℂ)‖ ≤ C * z.im) :
    ∀ z : ℂ, 0 < z.im → a ≤ |z.re| →
      (matrixQuadraticFormCLM v (M z)).im ≤ (‖matrixRealQuadraticFormCLM v‖ * C) * z.im := by
  intro z hz hza
  rw [im_matrixQuadraticFormCLM]
  calc
    _ ≤ ‖matrixRealQuadraticFormCLM v (imaginaryPart (M z) : Matrix n n ℂ)‖ :=
      le_abs_self _
    _ ≤ ‖matrixRealQuadraticFormCLM v‖ * ‖(imaginaryPart (M z) : Matrix n n ℂ)‖ :=
      (matrixRealQuadraticFormCLM v).le_opNorm _
    _ ≤ ‖matrixRealQuadraticFormCLM v‖ * (C * z.im) :=
      mul_le_mul_of_nonneg_left (hb z hz hza) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

/-- Every quadratic probe of a normalized matrix Herglotz function has
an actual unique positive compactly supported scalar Stieltjes measure.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1, polarization input.
This theorem supplies the matrix analytic foundation component.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem existsUnique_finiteMeasure_quadratic_stieltjes_eq
    (M : ℂ → Matrix n n ℂ)
    (hM : AnalyticOnNhd ℂ M {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → Matrix.PosSemidef (imaginaryPart (M z) : Matrix n n ℂ))
    (hlim : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) • M ((y : ℂ) * Complex.I))
      atTop (𝓝 (-1))) (κ : ℝ)
    (hb : ∀ a : ℝ, κ < a → ∃ C : ℝ, ∀ z : ℂ, 0 < z.im → a ≤ |z.re| →
      ‖(imaginaryPart (M z) : Matrix n n ℂ)‖ ≤ C * z.im)
    (v : n → ℂ) :
    ∃! μ : FiniteMeasure ℝ, μ.mass = quadraticProbeMass v ∧
      (∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Icc (-κ) κ) ∧
      ∀ z : ℂ, 0 < z.im → matrixQuadraticFormCLM v (M z) =
        ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(μ : Measure ℝ) := by
  have ha : AnalyticOnNhd ℂ (fun z => matrixQuadraticFormCLM v (M z)) {z : ℂ | 0 < z.im} :=
    fun z hz => ((matrixQuadraticFormCLM v).analyticAt _).comp (hM z hz)
  apply ha.existsUnique_finiteMeasure_stieltjes_eq_of_im_le
    (fun z hz => im_matrixQuadraticFormCLM_nonneg v (M z) (hpos z hz))
    (quadraticProbeMass v) (tendsto_mul_I_matrixQuadraticFormCLM M hlim v) κ
  intro a ha
  obtain ⟨C, hC⟩ := hb a ha
  exact ⟨‖matrixRealQuadraticFormCLM v‖ * C,
    im_matrixQuadraticFormCLM_le_mul_of_norm M v a C hC⟩

end Matrix
