import NLAlib.Probability.Concentration.Basic.MatrixCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import NLAlib.Probability.Rademacher.Core
import NLAlib.Matrix.OperatorTheory.EntropyNonnegative
import NLAlib.Matrix.OperatorTheory.JensenIsometricCompression

/-!
# Lemma 4.6.3 — Rademacher matrix mgf and cgf bounds

Main declaration: `NLAlib.rademacher_matrix_mgf_cgf_le`.

Atlas: `matrix-gaussian-series`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 4.6.3, printed p. 54.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {d : ℕ}

end NLAlib

open NLAlib

private lemma integrable_twoPoint (f : ℝ → ℝ) :
    Integrable f ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) :=
  Integrable.add_measure (Integrable.smul_measure (integrable_dirac (by simp)) (by simp))
    (Integrable.smul_measure (integrable_dirac (by simp)) (by simp))

/-- For a Rademacher `g` and Hermitian `A`, `𝔼 matrixExp (θ g A) ≼ matrixExp (θ²/2 • A²)` and its
logarithm is `≼ θ²/2 • A²`.

Tropp 2015, Lemma 4.6.3. Atlas: `matrix-gaussian-series`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 4*. -/
theorem NLAlib.rademacher_matrix_mgf_cgf_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (g : Ω → ℝ) (hLaw : IsRademacher μ g) (θ : ℝ) :
    (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) ≤ (matrixExp ((θ ^ 2 / 2) • A ^ 2)) ∧
    (matrixLog (∫ ω, matrixExp ((θ * g ω) • A) ∂μ)) ≤ ((θ ^ 2 / 2) • A ^ 2) := by
  have hs : ∀ t, Integrable (fun ω => Real.exp (t * (θ * g ω))) μ := by
    intro t
    have h1 := integrable_twoPoint (fun x => Real.exp (t * θ * x))
    have hmap := hLaw.map_eq
    rw [rademacherMeasure] at hmap
    rw [← hmap] at h1
    have h2 := (integrable_map_measure (by fun_prop) hLaw.aemeasurable).mp h1
    simpa [Function.comp_def, mul_assoc] using h2
  have hmgf : ∀ t, mgf g μ t = Real.cosh t := by
    intro t
    have h1 := integral_map (μ := μ) hLaw.aemeasurable (f := fun x => Real.exp (t * x))
      (by fun_prop)
    rw [mgf, ← h1, isRademacher_iff_map_eq.mp hLaw, rademacherMeasure, integral_add_measure, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, Real.cosh_eq]
    · simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul,
        mul_one, mul_neg]
      ring
    · exact Integrable.smul_measure (integrable_dirac (by simp)) (by simp)
    · exact Integrable.smul_measure (integrable_dirac (by simp)) (by simp)
  have hint : (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = cfc (fun x => Real.cosh (θ * x)) A := by
    rw [(integrable_and_integral_matrixExp_smul_eq_cfc_mgf μ A hA (fun ω => θ * g ω) hs).2]
    congr 1
    funext x
    rw [mgf_const_mul, hmgf]
  have hpt : ∀ x : ℝ, Real.cosh (θ * x) ≤ Real.exp (θ ^ 2 / 2 * x ^ 2) := by
    intro x
    calc Real.cosh (θ * x) ≤ Real.exp ((θ * x) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
      _ = Real.exp (θ ^ 2 / 2 * x ^ 2) := by congr 1; ring
  constructor
  · rw [hint, matrixExp_smul_sq_eq_cfc A hA]
    exact cfc_mono (fun x _ => hpt x)
  · rw [hint, smul_sq_eq_cfc A hA, matrixLog,
      ← cfc_comp' Real.log (fun x => Real.cosh (θ * x)) A
        (Real.continuousOn_log.mono (by
          rintro _ ⟨x, _, rfl⟩
          exact (Real.cosh_pos _).ne'))]
    refine cfc_mono (fun x _ => ?_) ?_
    · calc Real.log (Real.cosh (θ * x)) ≤ Real.log (Real.exp (θ ^ 2 / 2 * x ^ 2)) :=
            Real.log_le_log (Real.cosh_pos _) (hpt x)
        _ = θ ^ 2 / 2 * x ^ 2 := Real.log_exp _
    · exact (Real.continuousOn_log.comp (by fun_prop : Continuous fun x => Real.cosh (θ * x)).continuousOn
        (fun x _ => (Real.cosh_pos _).ne'))
