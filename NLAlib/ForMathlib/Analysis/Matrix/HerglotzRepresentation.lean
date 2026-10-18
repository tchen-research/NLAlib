import NLAlib.ForMathlib.Analysis.Matrix.HerglotzScalar
import NLAlib.ForMathlib.MeasureTheory.MatrixMeasurePolarization
import NLAlib.ForMathlib.MeasureTheory.PositiveMatrixMeasureStieltjes
import NLAlib.ForMathlib.MeasureTheory.PositiveMatrixMeasureUniqueness

/-!
# Positive matrix Stieltjes representation

A normalized analytic matrix function with positive imaginary part has
an actual positive matrix-valued Stieltjes measure. Uniform exterior
imaginary estimates give the compact spectral support. Scalar measures,
polarization compatibility, and entry measures are all constructed.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1, analytic bridge.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A normalized matrix Herglotz function has a positive matrix-valued
measure of total mass `I`, compact spectral support, and exact entrywise
Stieltjes integrals. No scalar measures or polarization premises are
assumed. Empty matrix dimensions are included.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1, matrix analytic bridge.
This theorem supplies the analytic foundation component.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem exists_positiveMatrixMeasure_stieltjes_eq
    (M : ℂ → Matrix n n ℂ)
    (hM : AnalyticOnNhd ℂ M {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → Matrix.PosSemidef (imaginaryPart (M z) : Matrix n n ℂ))
    (hlim : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) • M ((y : ℂ) * Complex.I))
      atTop (𝓝 (-1))) (κ : ℝ)
    (hb : ∀ a : ℝ, κ < a → ∃ C : ℝ, ∀ z : ℂ, 0 < z.im → a ≤ |z.re| →
      ‖(imaginaryPart (M z) : Matrix n n ℂ)‖ ≤ C * z.im) :
    ∃ P : PositiveMatrixMeasure ℝ n,
      P Set.univ = 1 ∧
      (∀ E : Set ℝ, MeasurableSet E → E ⊆ (Icc (-κ) κ)ᶜ → P E = 0) ∧
      ∀ z : ℂ, 0 < z.im → ∀ i j : n, P.entryStieltjesTransform z i j = M z i j := by
  classical
  have hs (v : n → ℂ) := (existsUnique_finiteMeasure_quadratic_stieltjes_eq
    M hM hpos hlim κ hb v).exists
  choose μ hμ using hs
  obtain ⟨P, hP⟩ := exists_positiveMatrixMeasure_of_quadratic_stieltjes M μ
    (fun v => (hμ v).2.2)
  have hmass : P Set.univ = 1 := by
    apply matrix_eq_of_isHermitian_of_re_dotProduct_mulVec_eq
      (P.isHermitian Set.univ MeasurableSet.univ) isHermitian_one
    intro v
    change P.quadraticForm v Set.univ = matrixRealQuadraticFormCLM v 1
    rw [hP v, Measure.toSignedMeasure_apply_measurable MeasurableSet.univ]
    change ((μ v).mass : ℝ) = (quadraticProbeMass v : ℝ)
    exact congrArg (fun r : NNReal => (r : ℝ)) (hμ v).1
  have hsupp (E : Set ℝ) (hE : MeasurableSet E) (hEc : E ⊆ (Icc (-κ) κ)ᶜ) : P E = 0 := by
    apply matrix_eq_of_isHermitian_of_re_dotProduct_mulVec_eq (P.isHermitian E hE) isHermitian_zero
    intro v
    have he : (μ v : Measure ℝ) E = 0 := by
      apply measure_mono_null hEc
      change (μ v : Measure ℝ) {x | x ∉ Icc (-κ) κ} = 0
      exact ae_iff.mp (hμ v).2.1
    change P.quadraticForm v E = (star v ⬝ᵥ ((0 : Matrix n n ℂ) *ᵥ v)).re
    rw [hP v, Measure.toSignedMeasure_apply_measurable hE]
    simp only [Measure.real, he, ENNReal.toReal_zero, Matrix.zero_mulVec, dotProduct_zero,
      Complex.zero_re]
  refine ⟨P, hmass, hsupp, ?_⟩
  intro z hz i j
  apply P.entryStieltjesTransform_eq_of_quadraticForm M ?_ hz i j
  intro v w hw
  rw [hP v, SignedMeasure.stieltjesTransform_toSignedMeasure]
  exact ((hμ v).2.2 w hw).symm

/-- The normalized positive matrix Stieltjes measure is unique, with
actual total mass `I`, compact support, and entrywise native complex
measure integrals. Source: Ajanki--Erdos--Kruger, Proposition 2.1.
This theorem supplies the analytic foundation component.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem existsUnique_positiveMatrixMeasure_stieltjes_eq
    (M : ℂ → Matrix n n ℂ)
    (hM : AnalyticOnNhd ℂ M {z : ℂ | 0 < z.im})
    (hpos : ∀ z : ℂ, 0 < z.im → Matrix.PosSemidef (imaginaryPart (M z) : Matrix n n ℂ))
    (hlim : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) • M ((y : ℂ) * Complex.I))
      atTop (𝓝 (-1))) (κ : ℝ)
    (hb : ∀ a : ℝ, κ < a → ∃ C : ℝ, ∀ z : ℂ, 0 < z.im → a ≤ |z.re| →
      ‖(imaginaryPart (M z) : Matrix n n ℂ)‖ ≤ C * z.im) :
    ∃! P : PositiveMatrixMeasure ℝ n,
      P Set.univ = 1 ∧
      (∀ E : Set ℝ, MeasurableSet E → E ⊆ (Icc (-κ) κ)ᶜ → P E = 0) ∧
      ∀ z : ℂ, 0 < z.im → ∀ i j : n, P.entryStieltjesTransform z i j = M z i j := by
  obtain ⟨P, hP⟩ := exists_positiveMatrixMeasure_stieltjes_eq M hM hpos hlim κ hb
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  apply Q.eq_of_entryStieltjesTransform_eq P
  intro z hz i j
  exact (hQ.2.2 z hz i j).trans (hP.2.2 z hz i j).symm

end Matrix
