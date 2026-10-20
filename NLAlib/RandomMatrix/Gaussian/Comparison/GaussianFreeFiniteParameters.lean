import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteInterpolation
import NLAlib.RandomMatrix.Gaussian.Basic.GUECoefficientParameters

/-! # Actual source parameter budgets throughout the finite-N interpolation

The two independent coefficient blocks are weighted by their real variance
weights. Their genuine variance and entry covariance therefore obey the
original coefficient budgets uniformly in q and the ensemble dimension.
Source: arXiv:2108.06312v2, Lemma 5.5 and the parameter step in Lemma 6.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Kronecker
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "M" => Matrix (d × n) (d × n) ℂ

private theorem variance_smul (C : M) (r : ℝ) :
    (r • C) * (r • C) = (r ^ 2) • (C * C) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]

omit [Fintype n] [Fintype d] [DecidableEq n] [DecidableEq d] in
private theorem covariance_outer_smul
    (C : Matrix (d × n) (d × n) ℂ) (r : ℝ) :
    Matrix.vecMulVec (fun ab : (d × n) × (d × n) => (r • C) ab.1 ab.2)
        (star (fun ab : (d × n) × (d × n) => (r • C) ab.1 ab.2)) =
      (r ^ 2) • Matrix.vecMulVec (fun ab : (d × n) × (d × n) => C ab.1 ab.2)
        (star (fun ab : (d × n) × (d × n) => C ab.1 ab.2)) := by
  ext ab ce
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, Matrix.smul_apply, Complex.real_smul,
    star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
  ring

omit [DecidableEq ι] in
/-- The actual variance of the true finite-N interpolation is exactly the
original variance tensor the ensemble identity, throughout the closed unit
interval. No Hermitian or positive-dimension hypothesis is required. -/
theorem coefficientVariance_gaussianFreeFiniteCoefficient
    (A : ι → Matrix d d ℂ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    coefficientVariance (gaussianFreeFiniteCoefficient (n := n) A q) =
      coefficientVariance A ⊗ₖ (1 : Matrix n n ℂ) := by
  have h1q : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have he : coefficientVariance (gaussianFreeFiniteCoefficient (n := n) A q) =
      q • coefficientVariance (fun ia : ι × n => A ia.1 ⊗ₖ (Matrix.single ia.2 ia.2 1 : Matrix n n ℂ)) +
      (1 - q) • coefficientVariance (fun ik : ι × GUECoordinate Unit n => A ik.1 ⊗ₖ gueCoefficientMatrix ik.2) := by
    simp only [coefficientVariance, Fintype.sum_sum_type, gaussianFreeFiniteCoefficient,
      variance_smul, Real.sq_sqrt hq, Real.sq_sqrt h1q, Finset.smul_sum]
  have hd := coefficientVariance_kronecker A (fun r : n => (Matrix.single r r 1 : Matrix n n ℂ))
  have hg := coefficientVariance_kronecker A (gueCoefficientMatrix (n := n))
  rw [he, hd, hg,
    coefficientVariance_diagonal_single, coefficientVariance_gueCoefficientMatrix,
    ← add_smul]
  simp

omit [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- The genuine entry covariance is the convex combination of the actual
diagonal tensor covariance and the actual GUE tensor covariance. -/
theorem coefficientCovariance_gaussianFreeFiniteCoefficient
    (A : ι → Matrix d d ℂ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    coefficientCovariance (gaussianFreeFiniteCoefficient (n := n) A q) =
      q • coefficientCovariance (fun ia : ι × n => A ia.1 ⊗ₖ (Matrix.single ia.2 ia.2 1 : Matrix n n ℂ)) +
      (1 - q) • coefficientCovariance (fun ik : ι × GUECoordinate Unit n => A ik.1 ⊗ₖ gueCoefficientMatrix ik.2) := by
  have h1q : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  simp only [coefficientCovariance_eq_sum_vecMulVec, Fintype.sum_sum_type,
    gaussianFreeFiniteCoefficient, covariance_outer_smul, Real.sq_sqrt hq,
    Real.sq_sqrt h1q, Finset.smul_sum]

open scoped Matrix.Norms.L2Operator in
/-- The actual interpolating matrix-series variance never exceeds the
original variance budget, uniformly in q and ensemble dimension. -/
theorem specNorm_coefficientVariance_gaussianFreeFiniteCoefficient_le
    (A : ι → Matrix d d ℂ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    specNorm (coefficientVariance (gaussianFreeFiniteCoefficient (n := n) A q)) ≤
      specNorm (coefficientVariance A) := by
  rw [coefficientVariance_gaussianFreeFiniteCoefficient A hq hq1, specNorm_kronecker]
  exact mul_le_of_le_one_right (specNorm_nonneg _) specNorm_one_le

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual unnormalized vectorized covariance never exceeds the original
covariance budget. This includes an empty ensemble, whose covariance is zero.
Source: arXiv:2108.06312v2, Lemma 5.5.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem specNorm_coefficientCovariance_gaussianFreeFiniteCoefficient_le
    (A : ι → Matrix d d ℂ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    specNorm (coefficientCovariance (gaussianFreeFiniteCoefficient (n := n) A q)) ≤
      specNorm (coefficientCovariance A) := by
  have h1q : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hg : specNorm (coefficientCovariance
      (fun ik : ι × GUECoordinate Unit n => A ik.1 ⊗ₖ gueCoefficientMatrix ik.2)) ≤
        specNorm (coefficientCovariance A) := by
    rw [specNorm_coefficientCovariance_kronecker_gueCoefficientMatrix]
    by_cases hn : Fintype.card n = 0
    · simp only [hn, Nat.cast_zero, div_zero]
      exact specNorm_nonneg _
    · exact div_le_self (specNorm_nonneg _) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  rw [coefficientCovariance_gaussianFreeFiniteCoefficient A hq hq1]
  calc
    _ ≤ ‖q • coefficientCovariance
          (fun ia : ι × n => A ia.1 ⊗ₖ (Matrix.single ia.2 ia.2 1 : Matrix n n ℂ))‖ +
        ‖(1 - q) • coefficientCovariance
          (fun ik : ι × GUECoordinate Unit n => A ik.1 ⊗ₖ gueCoefficientMatrix ik.2)‖ :=
      norm_add_le _ _
    _ = q * specNorm (coefficientCovariance
          (fun ia : ι × n => A ia.1 ⊗ₖ (Matrix.single ia.2 ia.2 1 : Matrix n n ℂ))) +
        (1 - q) * specNorm (coefficientCovariance
          (fun ik : ι × GUECoordinate Unit n => A ik.1 ⊗ₖ gueCoefficientMatrix ik.2)) := by
      simp only [norm_smul, Real.norm_of_nonneg hq, Real.norm_of_nonneg h1q,
        specNorm_eq_norm]
    _ ≤ q * specNorm (coefficientCovariance A) + (1 - q) * specNorm (coefficientCovariance A) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (specNorm_coefficientCovariance_kronecker_diagonal_single_le A) hq)
        (mul_le_mul_of_nonneg_left hg h1q)
    _ = _ := by ring

end NLAlib
