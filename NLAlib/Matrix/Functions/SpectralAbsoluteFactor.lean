import NLAlib.Matrix.Functions.PolynomialCalculus

/-!
# Covariance factors dominating a symmetric quadratic form

The spectral absolute value of a real symmetric matrix dominates its
negative. Factoring that absolute value gives Gaussian comparison
coordinates whose individual variances are bounded by the Euclidean row
norms of the original matrix. This is the covariance construction used in
van Handel, arXiv:1502.05003v4, Theorem 4.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An explicit factor of the spectral absolute value of a real symmetric
matrix, formed by scaling its orthonormal eigenvectors. -/
def spectralAbsoluteFactor {B : Matrix n n ℝ} (hB : B.IsHermitian) : Matrix n n ℝ :=
  (hB.eigenvectorUnitary : Matrix n n ℝ) *
    Matrix.diagonal (fun k => Real.sqrt |hB.eigenvalues k|)

private theorem gram_spectralAbsoluteFactor {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    spectralAbsoluteFactor hB * (spectralAbsoluteFactor hB)ᵀ =
      (hB.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal (fun k => |hB.eigenvalues k|) *
        (hB.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  simp only [spectralAbsoluteFactor, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.mul_assoc]
  congr 1
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  simp only [Real.mul_self_sqrt (abs_nonneg _)]

/-- The Gram matrix of the absolute spectral factor dominates the negative
of the original symmetric matrix in positive semidefinite order. -/
theorem posSemidef_gram_spectralAbsoluteFactor_add {B : Matrix n n ℝ}
    (hB : B.IsHermitian) :
    (spectralAbsoluteFactor hB * (spectralAbsoluteFactor hB)ᵀ + B).PosSemidef := by
  rw [gram_spectralAbsoluteFactor hB]
  conv =>
    arg 1
    rhs
    rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hB]
  rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
  have hdiag : (Matrix.diagonal (fun k => |hB.eigenvalues k| + hB.eigenvalues k)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun k => by linarith [neg_abs_le (hB.eigenvalues k)]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    using hdiag.conjTranspose_mul_mul_same (hB.eigenvectorUnitary : Matrix n n ℝ)ᵀ

/-- Squared linear combinations of the absolute spectral factor dominate
the negative quadratic form, with no nondegeneracy assumption. -/
theorem neg_quadForm_le_sum_sq_spectralAbsoluteFactor {B : Matrix n n ℝ}
    (hB : B.IsHermitian) (x : n → ℝ) :
    -quadForm B x ≤ ∑ k, (∑ i, spectralAbsoluteFactor hB i k * x i) ^ 2 := by
  have h := (posSemidef_gram_spectralAbsoluteFactor_add hB).quadForm_nonneg x
  simp only [quadForm, Matrix.add_mulVec, dotProduct_add] at h
  change 0 ≤ quadForm (spectralAbsoluteFactor hB * (spectralAbsoluteFactor hB)ᵀ) x +
    quadForm B x at h
  have hg : quadForm (spectralAbsoluteFactor hB * (spectralAbsoluteFactor hB)ᵀ) x =
      ∑ k, (∑ i, spectralAbsoluteFactor hB i k * x i) ^ 2 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
      dotProduct, Pi.star_apply, star_trivial, Matrix.mulVec, Matrix.transpose_apply, sq]
      using quadForm_conjTranspose_mul_self (spectralAbsoluteFactor hB)ᵀ x
  rw [hg] at h
  linarith

/-- Each row energy of the spectral absolute factor is bounded by the
Euclidean norm of that row of the original symmetric matrix. Thus the
Gaussian correction has the precise fourth-moment variance scale. -/
theorem sum_sq_spectralAbsoluteFactor_row_le {B : Matrix n n ℝ}
    (hB : B.IsHermitian) (i : n) :
    ∑ k, spectralAbsoluteFactor hB i k ^ 2 ≤ Real.sqrt (∑ j, B i j ^ 2) := by
  let U : Matrix n n ℝ := hB.eigenvectorUnitary
  let d : n → ℝ := hB.eigenvalues
  have hUU : U * Uᵀ = 1 := eigenvectorUnitary_mul_transpose_self hB
  have hUtU : Uᵀ * U = 1 := transpose_eigenvectorUnitary_mul_self hB
  have hspec : B = U * Matrix.diagonal d * Uᵀ :=
    eq_eigenvectorUnitary_mul_diagonal_mul_transpose hB
  have hrow : ∑ k, U i k ^ 2 = 1 := by
    have h := congrArg (fun M : Matrix n n ℝ => M i i) hUU
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, ← sq] using h
  have hgram : (U * Matrix.diagonal d) * (U * Matrix.diagonal d)ᵀ = B * Bᵀ := by
    rw [hspec]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U (Matrix.diagonal d * Uᵀ), hUtU, Matrix.one_mul]
  have hrow2 : ∑ k, (U i k * |d k|) ^ 2 = ∑ j, B i j ^ 2 := by
    have h := congrArg (fun M : Matrix n n ℝ => M i i) hgram
    simp only [Matrix.mul_apply, Matrix.transpose_apply, ← sq] at h
    change (∑ k, (U * Matrix.diagonal d) i k ^ 2) = ∑ j, B i j ^ 2 at h
    simpa only [Matrix.mul_diagonal,
      ← sq, mul_pow, sq_abs] using h
  have hfactor : (∑ k, spectralAbsoluteFactor hB i k ^ 2) = ∑ k, U i k * (U i k * |d k|) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [spectralAbsoluteFactor, Matrix.mul_diagonal, mul_pow,
      Real.sq_sqrt (abs_nonneg _)]
    dsimp [U, d]
    ring
  rw [hfactor]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => U i k)
    (fun k => U i k * |d k|)
  rw [hrow, hrow2, one_mul] at hcs
  exact Real.le_sqrt_of_sq_le hcs

end NLAlib
