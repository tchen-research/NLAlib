import NLAlib.Concentration.Matrix.Defs.ScalarLaws
import NLAlib.Concentration.Matrix.Defs.Calculus
import NLAlib.Concentration.Matrix.Defs.Dilation

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

private noncomputable def proj (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (i : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) * Matrix.single i i 1 *
    star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)

private lemma cfc_eq_sum (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = ∑ i, f (hA.eigenvalues i) • proj A hA i := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    ← Matrix.sum_single_eq_diagonal, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : Matrix.single i i ((RCLike.ofReal ∘ f ∘ hA.eigenvalues) i : ℂ)
      = f (hA.eigenvalues i) • (Matrix.single i i (1 : ℂ)) := by
    rw [Matrix.smul_single]; simp [Complex.real_smul]
  rw [this, proj, Matrix.mul_smul, Matrix.smul_mul]

private lemma integral_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (s : Ω → ℝ)
    (hs : ∀ t, Integrable (fun ω => Real.exp (t * s ω)) μ) :
    Integrable (fun ω => matrixExp (s ω • A)) μ ∧
    ∫ ω, matrixExp (s ω • A) ∂μ = cfc (fun t => mgf s μ t) A := by
  have h : (fun ω => matrixExp (s ω • A)) =
      fun ω => ∑ i, Real.exp (hA.eigenvalues i * s ω) • proj A hA i := by
    funext ω
    rw [matrixExp_smul_eq_cfc A hA, cfc_eq_sum A hA]
    simp only [mul_comm]
  rw [h]
  refine ⟨integrable_finsetSum _ (fun i _ => (hs _).smul_const _), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hs _).smul_const _), cfc_eq_sum A hA]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_smul_const]
  rfl

private lemma smul_sq_eq (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (c : ℝ) :
    c • A ^ 2 = cfc (fun x => c * x ^ 2) A := by
  rw [cfc_const_mul c (fun x : ℝ => x ^ 2) A, cfc_pow_id A 2 hA.isSelfAdjoint]

private lemma matrixExp_smul_sq_eq (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (c : ℝ) :
    matrixExp (c • A ^ 2) = cfc (fun x => Real.exp (c * x ^ 2)) A := by
  rw [matrixExp_smul_eq_cfc (A ^ 2) (hA.pow 2) c,
    ← cfc_comp_pow (fun y => Real.exp (c * y)) 2 A (by fun_prop) hA.isSelfAdjoint]

end NLAlib

open NLAlib

/-- For a standard Gaussian `g` and Hermitian `A`, `𝔼 matrixExp (θ g A) = matrixExp (θ²/2 • A²)` and
its logarithm is `θ²/2 • A²`.

Tropp 2015, Lemma 4.6.2. Atlas: `matrix-gaussian-series`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 4*. -/
theorem NLAlib.gaussian_matrix_mgf_cgf_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (g : Ω → ℝ) (hMeas : Measurable g) (hLaw : IsStandardGaussian μ g) (θ : ℝ) :
    (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = matrixExp ((θ ^ 2 / 2) • A ^ 2) ∧
    matrixLog (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = ((θ ^ 2 / 2) • A ^ 2) := by
  have hs : ∀ t, Integrable (fun ω => Real.exp (t * (θ * g ω))) μ := by
    intro t
    have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (t * θ)
    rw [← hLaw] at h1
    have h2 := (integrable_map_measure (by fun_prop) hMeas.aemeasurable).mp h1
    simpa [Function.comp_def, mul_assoc] using h2
  have hint := (integral_eq μ A hA (fun ω => θ * g ω) hs).2
  have hmain : (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = matrixExp ((θ ^ 2 / 2) • A ^ 2) := by
    rw [hint, matrixExp_smul_sq_eq A hA]
    congr 1
    funext x
    rw [mgf_const_mul, mgf_gaussianReal hLaw]
    congr 1
    simp only [NNReal.coe_one]
    ring
  refine ⟨hmain, ?_⟩
  rw [hmain]
  exact CFC.log_exp _ (IsSelfAdjoint.smul (isSelfAdjoint_iff.mpr (star_trivial _))
    (hA.isSelfAdjoint.pow 2))
