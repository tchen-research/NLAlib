import NLAlib.Probability.Concentration.Matrix.GaussianMaximumLaw

/-!
# Expected Gaussian maximum eigenvalues and scale decomposition

Centered Hermitian Gaussian laws have a nonnegative expected maximum
eigenvalue. Increasing the scale of the Gaussian part separates the original
shifted expected maximum from the excess-scale centered expected maximum.
These mean estimates preserve the exact constants in the Gaussian proxy bound.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- The maximum eigenvalue at any real Gaussian scale is integrable under a
finite weak quadratic variance bound. -/
theorem integrable_lambdaMax_add_smul_gaussian
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2) (c : ℝ) :
    Integrable (fun Z => lambdaMax (D + c • Z)) γ := by
  have h := (hasSubgaussianMGF_lambdaMax_add_smul_gaussian
    γ D hD hHerm hmean hσ hvariance c).integrable
  have hh := h.add (integrable_const (∫ H, lambdaMax (D + c • H) ∂γ))
  simpa only [Pi.add_def, sub_add_cancel] using hh

open scoped Matrix.Norms.L2Operator in
/-- A centered Hermitian Gaussian matrix has a nonnegative expected largest
eigenvalue, including a deterministic zero law. -/
theorem integral_lambdaMax_gaussian_nonneg
    (γ : Measure M) [IsGaussian γ]
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2) :
    0 ≤ ∫ Z, lambdaMax Z ∂γ := by
  let tr : M →L[ℝ] ℝ := Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  have htr := tr.integrable_comp (IsGaussian.integrable_id (μ := γ))
  have hmeantr := tr.integral_comp_comm (IsGaussian.integrable_id (μ := γ))
  simp only [id_eq] at htr hmeantr
  rw [hmean, map_zero] at hmeantr
  have hmax : Integrable (fun Z => lambdaMax Z) γ := by
    simpa only [zero_add] using integrable_lambdaMax_add_gaussian γ 0 Matrix.isHermitian_zero
      hHerm hmean hσ hvariance
  have hle : ∀ᵐ Z ∂γ, tr Z ≤ (Fintype.card n : ℝ) * lambdaMax Z := by
    filter_upwards [hHerm] with Z hZ
    change Z.trace.re ≤ _
    have he : Z.trace.re = ∑ i, hZ.eigenvalues i := by
      rw [hZ.trace_eq_sum_eigenvalues]
      simp
    rw [he]
    calc
      _ ≤ ∑ _i : n, lambdaMax Z := Finset.sum_le_sum fun i _ => hZ.eigenvalue_le_lambdaMax i
      _ = _ := by simp
  have hb := integral_mono_ae htr (hmax.const_mul (Fintype.card n : ℝ)) hle
  rw [hmeantr, integral_const_mul] at hb
  exact nonneg_of_mul_nonneg_right hb (Nat.cast_pos.mpr Fintype.card_pos)

open scoped Matrix.Norms.L2Operator in
/-- Increasing the Gaussian scale gives the exact expected-maximum
subadditivity bound used before scalar sub-gamma optimization.
Source: Tropp (2026), Proposition 4.7.
atlas: gaussian-proxy-eigenvalue-comparison (partial) -/
theorem integral_lambdaMax_smul_add_smul_gaussian_le
    (γ : Measure M) [IsGaussian γ] (D : M) (hD : D.IsHermitian)
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ Z, lambdaMax (a • D + b • Z) ∂γ) ≤
      a * (∫ Z, lambdaMax (D + Z) ∂γ) +
        (b - a) * (∫ Z, lambdaMax Z ∂γ) := by
  have hleft := integrable_lambdaMax_add_smul_gaussian γ (a • D)
    (hD.smul (IsSelfAdjoint.all a)) hHerm hmean hσ hvariance b
  have hbase := integrable_lambdaMax_add_gaussian γ D hD hHerm hmean hσ hvariance
  have hzero : Integrable (fun Z => lambdaMax Z) γ := by
    simpa only [zero_add] using integrable_lambdaMax_add_gaussian γ 0 Matrix.isHermitian_zero
      hHerm hmean hσ hvariance
  have hright := (hbase.const_mul a).add (hzero.const_mul (b - a))
  have hmono := integral_mono_ae hleft hright (hHerm.mono fun Z hZ =>
    lambdaMax_smul_add_smul_le D Z hD hZ ha hab)
  have he := integral_add (hbase.const_mul a) (hzero.const_mul (b - a))
  simp only [Pi.add_apply] at he hmono
  rw [he, integral_const_mul, integral_const_mul] at hmono
  exact hmono

end NLAlib
