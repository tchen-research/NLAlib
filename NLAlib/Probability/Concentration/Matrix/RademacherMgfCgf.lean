import NLAlib.Probability.Concentration.Matrix.SubgaussianMgfCgf
import NLAlib.Probability.Rademacher.Core
/-!
# Lemma 4.6.3 — Rademacher matrix mgf and cgf bounds

`integral_matrixExp_smul_le_of_hasLaw_rademacherMeasure`: `𝔼 matrixExp (θ r • A) ≼ matrixExp (θ²/2 • A²)`
for a Rademacher sign `r`, and `matrixLog_integral_matrixExp_smul_le_of_hasLaw_rademacherMeasure`
for its logarithm; both are the sub-Gaussian bounds of `SubgaussianMgfCgf` at proxy `1`.

Source: Tropp 2015, *An Introduction to Matrix Concentration Inequalities*, Lemma 4.6.3.
-/
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : Type*} [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- For a Rademacher sign `r` and Hermitian `A`, `𝔼 matrixExp (θ r • A) ≼ matrixExp (θ²/2 • A²)`.
Tropp 2015, Lemma 4.6.3. -/
theorem integral_matrixExp_smul_le_of_hasLaw_rademacherMeasure (A : Matrix d d ℂ)
    (hA : A.IsHermitian) {r : Ω → ℝ} (hr : HasLaw r rademacherMeasure μ) (θ : ℝ) :
    (∫ ω, matrixExp ((θ * r ω) • A) ∂μ) ≤ matrixExp ((θ ^ 2 / 2) • A ^ 2) :=
  integral_matrixExp_smul_le_of_hasSubgaussianMGF A hA
    (hasSubgaussianMGF_of_hasLaw_rademacherMeasure hr) θ

open scoped Matrix.Norms.L2Operator in
/-- For a Rademacher sign `r` and Hermitian `A`, `matrixLog (𝔼 matrixExp (θ r • A)) ≼ θ²/2 • A²`.
Tropp 2015, Lemma 4.6.3. -/
theorem matrixLog_integral_matrixExp_smul_le_of_hasLaw_rademacherMeasure (A : Matrix d d ℂ)
    (hA : A.IsHermitian) {r : Ω → ℝ} (hr : HasLaw r rademacherMeasure μ) (θ : ℝ) :
    matrixLog (∫ ω, matrixExp ((θ * r ω) • A) ∂μ) ≤ (θ ^ 2 / 2) • A ^ 2 :=
  have := hr.isProbabilityMeasure
  matrixLog_integral_matrixExp_smul_le_of_hasSubgaussianMGF A hA
    (hasSubgaussianMGF_of_hasLaw_rademacherMeasure hr) θ

end NLAlib
