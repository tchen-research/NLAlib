import NLAlib.Probability.Concentration.Basic.MatrixCalculus
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.MGFAnalytic
/-!
# Matrix mgf and cgf bounds for sub-Gaussian coefficients

For a `1`-sub-Gaussian scalar `g` and a Hermitian `A`, `𝔼 matrixExp (θ g • A) ≼ matrixExp (θ²/2 • A²)`
and `matrixLog (𝔼 matrixExp (θ g • A)) ≼ θ²/2 • A²`. The Gaussian (equality, Tropp 2015 Lemma 4.6.2)
and Rademacher (Lemma 4.6.3) cases are the corollaries in `GaussianMgfCgf` and `RademacherMgfCgf`.

Source: Tropp 2015, *An Introduction to Matrix Concentration Inequalities*, §4.6.
-/
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : Type*} [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- The matrix mgf of `θ g • A` is `cfc (mgf g μ (θ ·)) A` for a sub-Gaussian `g`. -/
theorem integral_matrixExp_smul_eq_cfc_of_hasSubgaussianMGF (A : Matrix d d ℂ) (hA : A.IsHermitian)
    {g : Ω → ℝ} {c : NNReal} (hg : HasSubgaussianMGF g c μ) (θ : ℝ) :
    (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) = cfc (fun x => mgf g μ (θ * x)) A := by
  have hs : ∀ t, Integrable (fun ω => Real.exp (t * (θ * g ω))) μ := by
    intro t
    simpa [mul_assoc] using hg.integrable_exp_mul (t * θ)
  rw [(integrable_and_integral_matrixExp_smul_eq_cfc_mgf μ A hA (fun ω => θ * g ω) hs).2]
  congr 1
  funext x
  rw [mgf_const_mul, mul_comm]

open scoped Matrix.Norms.L2Operator in
/-- **Matrix mgf bound for a sub-Gaussian coefficient**: for `HasSubgaussianMGF g 1 μ` and
Hermitian `A`, `𝔼 matrixExp (θ g • A) ≼ matrixExp (θ²/2 • A²)`. Tropp 2015, Lemmas 4.6.2–4.6.3
(the Gaussian and Rademacher cases). -/
theorem integral_matrixExp_smul_le_of_hasSubgaussianMGF (A : Matrix d d ℂ) (hA : A.IsHermitian)
    {g : Ω → ℝ} (hg : HasSubgaussianMGF g 1 μ) (θ : ℝ) :
    (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) ≤ matrixExp ((θ ^ 2 / 2) • A ^ 2) := by
  have hcont : Continuous (fun x : ℝ => mgf g μ (θ * x)) :=
    (continuous_mgf hg.integrable_exp_mul).comp (continuous_const.mul continuous_id)
  rw [integral_matrixExp_smul_eq_cfc_of_hasSubgaussianMGF A hA hg θ, matrixExp_smul_sq_eq_cfc A hA]
  refine cfc_mono (fun x _ => ?_) hcont.continuousOn (by fun_prop)
  calc mgf g μ (θ * x) ≤ Real.exp (1 * (θ * x) ^ 2 / 2) := by simpa using hg.mgf_le (θ * x)
    _ = Real.exp (θ ^ 2 / 2 * x ^ 2) := by congr 1; ring

open scoped Matrix.Norms.L2Operator in
/-- **Matrix cgf bound for a sub-Gaussian coefficient**: for `HasSubgaussianMGF g 1 μ`, `μ ≠ 0` and
Hermitian `A`, `matrixLog (𝔼 matrixExp (θ g • A)) ≼ θ²/2 • A²`. Tropp 2015, Lemmas 4.6.2–4.6.3. -/
theorem matrixLog_integral_matrixExp_smul_le_of_hasSubgaussianMGF [NeZero μ]
    (A : Matrix d d ℂ) (hA : A.IsHermitian) {g : Ω → ℝ} (hg : HasSubgaussianMGF g 1 μ) (θ : ℝ) :
    matrixLog (∫ ω, matrixExp ((θ * g ω) • A) ∂μ) ≤ (θ ^ 2 / 2) • A ^ 2 := by
  have hpos : ∀ x : ℝ, 0 < mgf g μ (θ * x) := fun x =>
    mgf_pos' (NeZero.ne μ) (hg.integrable_exp_mul (θ * x))
  rw [integral_matrixExp_smul_eq_cfc_of_hasSubgaussianMGF A hA hg θ, smul_sq_eq_cfc A hA, matrixLog,
    ← cfc_comp' Real.log (fun x => mgf g μ (θ * x)) A
      (Real.continuousOn_log.mono (by
        rintro _ ⟨x, _, rfl⟩
        exact (hpos x).ne'))]
  have hcont : Continuous (fun x : ℝ => mgf g μ (θ * x)) :=
    (continuous_mgf hg.integrable_exp_mul).comp (continuous_const.mul continuous_id)
  refine cfc_mono (fun x _ => ?_) ?_ (by fun_prop)
  · calc Real.log (mgf g μ (θ * x)) ≤ Real.log (Real.exp (1 * (θ * x) ^ 2 / 2)) :=
          Real.log_le_log (hpos x) (by simpa using hg.mgf_le (θ * x))
      _ = θ ^ 2 / 2 * x ^ 2 := by rw [Real.log_exp]; ring
  · exact Real.continuousOn_log.comp hcont.continuousOn (fun x _ => (hpos x).ne')

end NLAlib
