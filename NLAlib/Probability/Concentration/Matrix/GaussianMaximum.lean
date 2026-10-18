import NLAlib.Matrix.Norms.QuadraticSeries
import NLAlib.Matrix.Spectral.ExtremePerturbation
import NLAlib.Probability.Gaussian.Concentration.LipschitzConcentration
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian maximum-eigenvalue concentration with quadratic weak variance

The variance of each unit-vector quadratic form is exactly its coefficient
square energy. Uniformly bounding those variances makes the largest eigenvalue
of an affine Hermitian Gaussian series Lipschitz with the same variance scale.
The centered sub-Gaussian MGF includes zero variance and empty series.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

omit [DecidableEq n] in
/-- The actual variance of a Gaussian-series unit-vector quadratic form is
the sum of the squared real quadratic forms of its Hermitian coefficients.
The identity holds for all vectors and includes empty coefficient families. -/
theorem variance_re_quadForm_gaussianSeries
    (A : ι → Matrix n n ℂ) (u : n → ℂ) :
    Var[fun x : ι → ℝ => (quadForm (∑ i, x i • A i) u).re; gaussianVector ι] =
      ∑ i, (quadForm (A i) u).re ^ 2 := by
  classical
  have he : (fun x : ι → ℝ => (quadForm (∑ i, x i • A i) u).re) =
      ∑ i, (fun x : ι → ℝ => (quadForm (A i) u).re * x i) := by
    ext x
    simp only [Finset.sum_apply, quadForm, Matrix.sum_mulVec, dotProduct_sum,
      Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul,
      Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [he, variance_sum_pi]
  · change (∑ i, Var[fun x : ℝ => (quadForm (A i) u).re * id x; gaussianReal 0 1]) = _
    simp only [variance_const_mul, variance_id_gaussianReal, NNReal.coe_one, mul_one]
  · intro i
    exact (IsGaussian.memLp_two_id (μ := gaussianReal 0 1)).const_mul _

/-- Uniform weak quadratic variance bounds give the sharp Euclidean
Lipschitz bound for the maximum eigenvalue of every deterministic affine
Hermitian series. -/
theorem abs_lambdaMax_affineSeries_sub_le_of_quadratic_energy [Nonempty n]
    (D : Matrix n n ℂ) (hD : D.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (henergy : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      ∑ i, (quadForm (A i) u).re ^ 2 ≤ σ ^ 2) (x y : ι → ℝ) :
    |lambdaMax (D + ∑ i, x i • A i) - lambdaMax (D + ∑ i, y i • A i)| ≤
      σ * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  classical
  have hx : (D + ∑ i, x i • A i).IsHermitian :=
    hD.add (isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _))
  have hy : (D + ∑ i, y i • A i).IsHermitian :=
    hD.add (isSelfAdjoint_sum _ fun i _ => (hA i).smul (IsSelfAdjoint.all _))
  have hd : (D + ∑ i, x i • A i) - (D + ∑ i, y i • A i) =
      ∑ i, (x i - y i) • A i := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  exact (abs_lambdaMax_sub_le_specNorm_sub _ _ hx hy).trans
    (hd ▸ specNorm_sum_smul_le_of_quadratic_energy A hA hσ henergy (fun i => x i - y i))

/-- The centered maximum eigenvalue of an affine Hermitian standard Gaussian
series has a sub-Gaussian MGF with the unit quadratic-form weak variance bound.
No additional moment, smoothness, positivity of the variance, or nonempty
coefficient-family assumption is needed. Source: Gaussian concentration used
in Tropp (2026), Proposition 4.7.
atlas: gaussian-proxy-eigenvalue-comparison (partial) -/
theorem hasSubgaussianMGF_lambdaMax_affineSeries_of_quadratic_energy [Nonempty n]
    (D : Matrix n n ℂ) (hD : D.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (henergy : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      ∑ i, (quadForm (A i) u).re ^ 2 ≤ σ ^ 2) :
    HasSubgaussianMGF
      (fun x : ι → ℝ => lambdaMax (D + ∑ i, x i • A i) -
        ∫ y, lambdaMax (D + ∑ i, y i • A i) ∂gaussianVector ι)
      ⟨σ ^ 2, sq_nonneg σ⟩ (gaussianVector ι) := by
  classical
  simpa only [one_mul] using hasSubgaussianMGF_of_logSobolev
    hasEuclideanLogSobolev_gaussianVector
    (fun x : ι → ℝ => lambdaMax (D + ∑ i, x i • A i)) σ hσ
    (abs_lambdaMax_affineSeries_sub_le_of_quadratic_energy D hD A hA hσ henergy)

/-- A uniform bound on the actual unit quadratic-form variances of the
Gaussian series gives the same centered maximum-eigenvalue sub-Gaussian MGF.
This states the weak-variance assumption directly as a variance of the
quadratic form, rather than a coefficient or bilinear substitute.
atlas: gaussian-proxy-eigenvalue-comparison (partial) -/
theorem hasSubgaussianMGF_lambdaMax_affineSeries_of_quadratic_variance [Nonempty n]
    (D : Matrix n n ℂ) (hD : D.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun x : ι → ℝ => (quadForm (∑ i, x i • A i) u).re; gaussianVector ι] ≤ σ ^ 2) :
    HasSubgaussianMGF
      (fun x : ι → ℝ => lambdaMax (D + ∑ i, x i • A i) -
        ∫ y, lambdaMax (D + ∑ i, y i • A i) ∂gaussianVector ι)
      ⟨σ ^ 2, sq_nonneg σ⟩ (gaussianVector ι) := by
  apply hasSubgaussianMGF_lambdaMax_affineSeries_of_quadratic_energy D hD A hA hσ
  simpa only [variance_re_quadForm_gaussianSeries] using hvariance

/-- The weak quadratic variance bound ensures integrability of the maximum
eigenvalue of an affine Hermitian Gaussian series. -/
theorem integrable_lambdaMax_affineSeries_of_quadratic_energy [Nonempty n]
    (D : Matrix n n ℂ) (hD : D.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (henergy : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      ∑ i, (quadForm (A i) u).re ^ 2 ≤ σ ^ 2) :
    Integrable (fun x : ι → ℝ => lambdaMax (D + ∑ i, x i • A i)) (gaussianVector ι) := by
  exact integrable_of_lipschitz_gaussianVector _ σ hσ
    (abs_lambdaMax_affineSeries_sub_le_of_quadratic_energy D hD A hA hσ henergy)

/-- The uncentered MGF of an affine Gaussian maximum eigenvalue is bounded
by its actual mean and the weak quadratic variance budget, at every real
parameter. The zero-variance endpoint is included.
atlas: gaussian-proxy-eigenvalue-comparison (partial) -/
theorem integral_exp_mul_lambdaMax_affineSeries_le_of_quadratic_energy [Nonempty n]
    (D : Matrix n n ℂ) (hD : D.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (henergy : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      ∑ i, (quadForm (A i) u).re ^ 2 ≤ σ ^ 2) (t : ℝ) :
    (∫ x, Real.exp (t * lambdaMax (D + ∑ i, x i • A i)) ∂gaussianVector ι) ≤
      Real.exp (t * (∫ x, lambdaMax (D + ∑ i, x i • A i) ∂gaussianVector ι) +
        t ^ 2 * σ ^ 2 / 2) := by
  let f : (ι → ℝ) → ℝ := fun x => lambdaMax (D + ∑ i, x i • A i)
  let m : ℝ := ∫ x, f x ∂gaussianVector ι
  have hsg := hasSubgaussianMGF_lambdaMax_affineSeries_of_quadratic_energy D hD A hA hσ henergy
  have he : mgf f (gaussianVector ι) t =
      mgf (fun x => f x - m) (gaussianVector ι) t * Real.exp (t * m) := by
    simpa only [sub_add_cancel] using
      (mgf_add_const (X := fun x => f x - m) (μ := gaussianVector ι) (t := t) m)
  change mgf f (gaussianVector ι) t ≤ Real.exp (t * m + t ^ 2 * σ ^ 2 / 2)
  rw [he]
  calc
    _ ≤ Real.exp (σ ^ 2 * t ^ 2 / 2) * Real.exp (t * m) :=
      mul_le_mul_of_nonneg_right (hsg.mgf_le t) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end NLAlib
