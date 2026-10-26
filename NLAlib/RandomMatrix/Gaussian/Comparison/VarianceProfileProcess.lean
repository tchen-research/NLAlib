import NLAlib.Matrix.Functions.SpectralAbsoluteFactor
import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricQuadraticForms
import NLAlib.Probability.Gaussian.Comparison.SudakovFernique

/-!
# Gaussian process comparison for a variance profile

An explicit two-row standard Gaussian sample realizes the comparison
process for symmetric Gaussian quadratic forms. Its first row supplies
the nonlinear Euclidean deformation, and its second supplies the
spectral absolute-value covariance correction. All increment comparisons
are computed from these actual independent Gaussian coordinates.

Source: van Handel, arXiv:1502.05003v4, Lemma 4.6 and Theorem 4.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace NLAlib

variable {n : ℕ}

/-- Squaring a symmetric coefficient profile entry by entry gives a real
Hermitian variance matrix. -/
theorem isHermitian_varianceProfile_sq (b : Matrix (Fin n) (Fin n) ℝ) (hb : b.IsSymm) :
    (Matrix.of fun i j => b i j ^ 2).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply, hb.apply i j]

/-- Explicit independent-coordinate coefficients of the comparison
process: the deformed linear process and its Gaussian quadratic correction. -/
def varianceProfileComparisonCoefficient (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (v : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun r k => if r = 0 then 2 * varianceProfileDeformation B v k
    else ∑ i, spectralAbsoluteFactor hB i k * v i ^ 2

/-- The exact increment variance of the explicit comparison process. -/
theorem sum_sq_varianceProfileComparisonCoefficient_sub
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (v w : Fin n → ℝ) :
    (∑ r, ∑ k, (varianceProfileComparisonCoefficient B hB v r k -
      varianceProfileComparisonCoefficient B hB w r k) ^ 2) =
      4 * (∑ i, (varianceProfileDeformation B v i - varianceProfileDeformation B w i) ^ 2) +
        ∑ k, (∑ i, spectralAbsoluteFactor hB i k * (v i ^ 2 - w i ^ 2)) ^ 2 := by
  rw [Fin.sum_univ_two]
  simp only [varianceProfileComparisonCoefficient, Matrix.of_apply, if_true]
  norm_num only [show (1 : Fin 2) ≠ 0 by decide, if_false]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The explicit covariance correction dominates the negative quadratic
term of the variance-profile increment inequality. -/
theorem varianceProfileQuadraticDistanceSq_le_comparisonCoefficient
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian)
    (hB0 : ∀ i j, 0 ≤ B i j) (v w : Fin n → ℝ) :
    varianceProfileQuadraticDistanceSq B v w ≤
      ∑ r, ∑ k, (varianceProfileComparisonCoefficient B hB v r k -
        varianceProfileComparisonCoefficient B hB w r k) ^ 2 := by
  rw [sum_sq_varianceProfileComparisonCoefficient_sub]
  have hsymm : B.IsSymm := Matrix.isHermitian_iff_isSymm.mp hB
  have hgeo := varianceProfileQuadraticDistanceSq_le_deformation B hB0 hsymm v w
  have hcor := neg_quadForm_le_sum_sq_spectralAbsoluteFactor hB (fun i => v i ^ 2 - w i ^ 2)
  have hform : quadForm B (fun i => v i ^ 2 - w i ^ 2) =
      varianceProfileSquareDifferenceForm B v w := by
    simp only [quadForm_eq_sum_mul_mul, star_trivial, varianceProfileSquareDifferenceForm]
  rw [hform] at hcor
  linarith

/-- The actual independent Gaussian quadratic-form coefficients are
dominated by the explicitly realized comparison process coefficients. -/
theorem sum_sq_symmetricGaussianQuadraticCoefficient_sub_le_comparison
    (b : Matrix (Fin n) (Fin n) ℝ) (hb : b.IsSymm) (v w : Fin n → ℝ) :
    (∑ i, ∑ j, (symmetricGaussianQuadraticCoefficient b v i j -
      symmetricGaussianQuadraticCoefficient b w i j) ^ 2) ≤
      ∑ r, ∑ k, (varianceProfileComparisonCoefficient (Matrix.of fun i j => b i j ^ 2)
        (isHermitian_varianceProfile_sq b hb) v r k -
        varianceProfileComparisonCoefficient (Matrix.of fun i j => b i j ^ 2)
          (isHermitian_varianceProfile_sq b hb) w r k) ^ 2 := by
  exact (sum_sq_symmetricGaussianQuadraticCoefficient_sub_le b hb v w).trans
    (varianceProfileQuadraticDistanceSq_le_comparisonCoefficient _ _ (fun i j => sq_nonneg _) v w)

/-- On every finite family of vectors, the expected maximum of the
actual symmetric Gaussian quadratic forms is bounded by that of the
explicit two-row Gaussian comparison process. No covariance or moment
estimate is assumed: both are computed from the standard Gaussian law. -/
theorem integral_iSup_quadForm_symmetricGaussianMatrix_le_comparison
    {ι : Type*} [Fintype ι] (b : Matrix (Fin n) (Fin n) ℝ) (hb : b.IsSymm)
    (v : ι → Fin n → ℝ) :
    (∫ G, (⨆ t, quadForm (symmetricGaussianMatrix b G) (v t))
      ∂gaussianMatrix (Fin n) (Fin n)) ≤
      ∫ H, (⨆ t, linForm (varianceProfileComparisonCoefficient
        (Matrix.of fun i j => b i j ^ 2) (isHermitian_varianceProfile_sq b hb) (v t)) H)
        ∂gaussianMatrix (Fin 2) (Fin n) := by
  simp_rw [quadForm_symmetricGaussianMatrix_eq_linForm]
  refine sudakov_fernique_inequality _ _
    (hasGaussianLaw_linForm_gaussianMatrix _) (hasGaussianLaw_linForm_gaussianMatrix _)
    (fun t => integral_linForm_gaussianMatrix _) (fun t => integral_linForm_gaussianMatrix _) ?_
  intro s t
  simp_rw [linForm_sub_linForm]
  rw [integral_linForm_sq_gaussianMatrix, integral_linForm_sq_gaussianMatrix]
  exact sum_sq_symmetricGaussianQuadraticCoefficient_sub_le_comparison b hb (v s) (v t)

/-- The same explicit comparison process also controls the expected
maximum of the negatives of the actual quadratic forms, since negating
all independent-coordinate coefficients preserves the increment metric. -/
theorem integral_iSup_neg_quadForm_symmetricGaussianMatrix_le_comparison
    {ι : Type*} [Fintype ι] (b : Matrix (Fin n) (Fin n) ℝ) (hb : b.IsSymm)
    (v : ι → Fin n → ℝ) :
    (∫ G, (⨆ t, -quadForm (symmetricGaussianMatrix b G) (v t))
      ∂gaussianMatrix (Fin n) (Fin n)) ≤
      ∫ H, (⨆ t, linForm (varianceProfileComparisonCoefficient
        (Matrix.of fun i j => b i j ^ 2) (isHermitian_varianceProfile_sq b hb) (v t)) H)
        ∂gaussianMatrix (Fin 2) (Fin n) := by
  have hneg (t : ι) (G : Matrix (Fin n) (Fin n) ℝ) :
      -quadForm (symmetricGaussianMatrix b G) (v t) =
        linForm (-symmetricGaussianQuadraticCoefficient b (v t)) G := by
    rw [quadForm_symmetricGaussianMatrix_eq_linForm]
    simp only [linForm, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
  simp_rw [hneg]
  refine sudakov_fernique_inequality _ _
    (hasGaussianLaw_linForm_gaussianMatrix _) (hasGaussianLaw_linForm_gaussianMatrix _)
    (fun t => integral_linForm_gaussianMatrix _) (fun t => integral_linForm_gaussianMatrix _) ?_
  intro s t
  simp_rw [linForm_sub_linForm]
  rw [integral_linForm_sq_gaussianMatrix, integral_linForm_sq_gaussianMatrix]
  refine le_trans (le_of_eq ?_)
    (sum_sq_symmetricGaussianQuadraticCoefficient_sub_le_comparison b hb (v s) (v t))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (-symmetricGaussianQuadraticCoefficient b (v s) i j -
    -symmetricGaussianQuadraticCoefficient b (v t) i j) ^ 2 = _
  ring

/-- The realized comparison process splits exactly into its deformed
linear term and the squared-coordinate Gaussian correction. -/
theorem linForm_varianceProfileComparisonCoefficient
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (v : Fin n → ℝ)
    (H : Matrix (Fin 2) (Fin n) ℝ) :
    linForm (varianceProfileComparisonCoefficient B hB v) H =
      2 * (∑ i, H 0 i * varianceProfileDeformation B v i) +
        ∑ i, v i ^ 2 * (∑ k, spectralAbsoluteFactor hB i k * H 1 k) := by
  rw [linForm, Fin.sum_univ_two]
  simp only [varianceProfileComparisonCoefficient, Matrix.of_apply, if_true]
  norm_num only [show (1 : Fin 2) ≠ 0 by decide, if_false]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- On the Euclidean unit ball, the actual comparison process is bounded
by twice the largest weighted Gaussian row radius and the largest
coordinate of the covariance correction. -/
theorem linForm_varianceProfileComparisonCoefficient_le
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (hB0 : ∀ i j, 0 ≤ B i j)
    (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 ≤ 1) (H : Matrix (Fin 2) (Fin n) ℝ)
    (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hrows : ∀ j, varianceProfileRadius B (H 0) j ≤ R)
    (hcorr : ∀ i, ∑ k, spectralAbsoluteFactor hB i k * H 1 k ≤ M) :
    linForm (varianceProfileComparisonCoefficient B hB v) H ≤ 2 * R + M := by
  have hsymm : B.IsSymm := Matrix.isHermitian_iff_isSymm.mp hB
  have hrowSq (j : Fin n) : ∑ i, B i j * H 0 i ^ 2 ≤ R ^ 2 := by
    have hsq := pow_le_pow_left₀ (varianceProfileRadius_nonneg B (H 0) j) (hrows j) 2
    rw [varianceProfileRadius_sq B hB0] at hsq
    simpa only [hsymm.apply j _] using hsq
  have hfirst := sum_mul_varianceProfileDeformation_le B hB0 v (H 0) hv R hR hrowSq
  have hsecond : (∑ i, v i ^ 2 * (∑ k, spectralAbsoluteFactor hB i k * H 1 k)) ≤ M := by
    calc _ ≤ ∑ i, v i ^ 2 * M := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hcorr i) (sq_nonneg _)
      _ = (∑ i, v i ^ 2) * M := (Finset.sum_mul ..).symm
      _ ≤ M := by nlinarith
  rw [linForm_varianceProfileComparisonCoefficient]
  linarith

end NLAlib
