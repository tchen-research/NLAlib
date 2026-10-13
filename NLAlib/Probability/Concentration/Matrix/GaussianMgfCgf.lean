import NLAlib.Probability.Concentration.Basic.ScalarLaws
import NLAlib.Probability.Concentration.Basic.MatrixCalculus
/-!
# Lemma 4.6.2 — Gaussian matrix mgf and cgf identities

Main declaration: `NLAlib.gaussian_matrix_mgf_cgf_eq`.

Atlas: `matrix-gaussian-series`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Lemma 4.6.2, printed pp. 52–53.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {d : ℕ}

end NLAlib

open NLAlib

/-- For a standard Gaussian `g` and Hermitian `A`, `𝔼 matrixExp (θ g A) = matrixExp (θ²/2 • A²)` and
its logarithm is `θ²/2 • A²`.

Tropp 2015, Lemma 4.6.2. Atlas: `matrix-gaussian-series`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 4*. -/
theorem NLAlib.gaussian_matrix_mgf_cgf_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (g : Ω → ℝ) (hLaw : IsStandardGaussian μ g) (θ : ℝ) :
    (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = matrixExp ((θ ^ 2 / 2) • A ^ 2) ∧
    matrixLog (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = ((θ ^ 2 / 2) • A ^ 2) := by
  have hs : ∀ t, Integrable (fun ω => Real.exp (t * (θ * g ω))) μ := by
    intro t
    have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (t * θ)
    rw [← hLaw.map_eq] at h1
    have h2 := (integrable_map_measure (by fun_prop) hLaw.aemeasurable).mp h1
    simpa [Function.comp_def, mul_assoc] using h2
  have hint := (integrable_and_integral_matrixExp_smul_eq_cfc_mgf μ A hA (fun ω => θ * g ω) hs).2
  have hmain : (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = matrixExp ((θ ^ 2 / 2) • A ^ 2) := by
    rw [hint, matrixExp_smul_sq_eq_cfc A hA]
    congr 1
    funext x
    rw [mgf_const_mul, mgf_gaussianReal hLaw.map_eq]
    congr 1
    simp only [NNReal.coe_one]
    ring
  refine ⟨hmain, ?_⟩
  rw [hmain]
  exact CFC.log_exp _ (IsSelfAdjoint.smul (isSelfAdjoint_iff.mpr (star_trivial _))
    (hA.isSelfAdjoint.pow 2))
