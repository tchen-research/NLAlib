import NLAlib.Probability.Concentration.Basic.ScalarLaws
import NLAlib.Probability.Concentration.Matrix.SubgaussianMgfCgf
/-!
# Lemma 4.6.2 — Gaussian matrix mgf and cgf identities

`integral_matrixExp_smul_of_hasLaw_gaussianReal`: `𝔼 matrixExp (θ g • A) = matrixExp (θ²/2 • A²)`
for a standard Gaussian `g`, and `matrixLog_integral_matrixExp_smul_of_hasLaw_gaussianReal` for its
logarithm.

Source: Tropp 2015, *An Introduction to Matrix Concentration Inequalities*, Lemma 4.6.2.
-/
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : Type*} [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- For a standard Gaussian `g` and Hermitian `A`, `𝔼 matrixExp (θ g • A) = matrixExp (θ²/2 • A²)`.
Tropp 2015, Lemma 4.6.2. -/
theorem integral_matrixExp_smul_of_hasLaw_gaussianReal (A : Matrix d d ℂ) (hA : A.IsHermitian)
    {g : Ω → ℝ} (hg : HasLaw g (gaussianReal 0 1) μ) (θ : ℝ) :
    (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = matrixExp ((θ ^ 2 / 2) • A ^ 2) := by
  rw [integral_matrixExp_smul_eq_cfc_of_hasSubgaussianMGF A hA
    (hasSubgaussianMGF_of_hasLaw_gaussianReal hg) θ, matrixExp_smul_sq_eq_cfc A hA]
  congr 1
  funext x
  rw [mgf_gaussianReal hg.map_eq]
  congr 1
  simp only [NNReal.coe_one]
  ring

open scoped Matrix.Norms.L2Operator in
/-- For a standard Gaussian `g` and Hermitian `A`, `matrixLog (𝔼 matrixExp (θ g • A)) = θ²/2 • A²`.
Tropp 2015, Lemma 4.6.2. -/
theorem matrixLog_integral_matrixExp_smul_of_hasLaw_gaussianReal (A : Matrix d d ℂ)
    (hA : A.IsHermitian) {g : Ω → ℝ} (hg : HasLaw g (gaussianReal 0 1) μ) (θ : ℝ) :
    matrixLog (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = (θ ^ 2 / 2) • A ^ 2 := by
  rw [integral_matrixExp_smul_of_hasLaw_gaussianReal A hA hg θ]
  exact CFC.log_exp _ (IsSelfAdjoint.smul (isSelfAdjoint_iff.mpr (star_trivial _))
    (hA.isSelfAdjoint.pow 2))

end NLAlib
