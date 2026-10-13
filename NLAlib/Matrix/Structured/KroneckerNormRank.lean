import NLAlib.Matrix.Structured.KroneckerSpectrum
import NLAlib.Matrix.Spectral.QuadraticProbe
import NLAlib.ForMathlib.Analysis.FinitePairNorm
/-!
# Spectral norm and rank of Kronecker products

The real Gram spectral decomposition proves exact spectral-norm and rank
multiplication for arbitrary rectangular matrices. All finite indices are
allowed, including empty dimensions and zero ranks.
Source: Horn–Johnson 1991, Theorem 4.2.15. Atlas: `kronecker-spectral`.
-/

noncomputable section
open scoped Matrix Kronecker

namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- Spectral norms of real symmetric Kronecker factors multiply exactly.
Horn–Johnson 1991, Theorem 4.2.12; no positivity or nonempty dimension condition.
-/
theorem specNorm_kronecker_of_isHermitian {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    specNorm (A ⊗ₖ B) = specNorm A * specNorm B := by
  have hP := hasOrthonormalCols_kronecker
    (transpose_eigenvectorUnitary_mul_self hA) (transpose_eigenvectorUnitary_mul_self hB)
  calc
    _ = ‖(fun ij : m × n => hA.eigenvalues ij.1 * hB.eigenvalues ij.2)‖ := by
      conv_lhs => rw [eq_eigenvectorUnitary_kronecker_mul_diagonal_mul_transpose hA hB,
        specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hP,
        specNorm_mul_left_of_hasOrthonormalCols hP,
        specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
    _ = ‖hA.eigenvalues‖ * ‖hB.eigenvalues‖ := norm_pair_mul _ _
    _ = _ := by rw [← specNorm_eq_norm_eigenvalues hA, ← specNorm_eq_norm_eigenvalues hB]

open scoped Matrix.Norms.L2Operator in
/-- Spectral norms multiply exactly under a Kronecker product of arbitrary finite
rectangular real matrices. Horn–Johnson 1991, Theorem 4.2.15. Empty dimensions,
zero matrices, and rank deficient factors are included.
atlas: kronecker-spectral -/
theorem specNorm_kronecker {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A : Matrix m n ℝ) (B : Matrix p q ℝ) :
    specNorm (A ⊗ₖ B) = specNorm A * specNorm B := by
  have hA : (Aᵀ * A).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self A
  have hB : (Bᵀ * B).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self B
  have hsq : specNorm (A ⊗ₖ B) ^ 2 = (specNorm A * specNorm B) ^ 2 := by
    rw [specNorm_sq_eq_specNorm_transpose_mul_self, ← Matrix.kroneckerMap_transpose,
      ← Matrix.mul_kronecker_mul, specNorm_kronecker_of_isHermitian hA hB,
      ← specNorm_sq_eq_specNorm_transpose_mul_self,
      ← specNorm_sq_eq_specNorm_transpose_mul_self, mul_pow]
  nlinarith [specNorm_nonneg (A ⊗ₖ B),
    mul_nonneg (specNorm_nonneg A) (specNorm_nonneg B)]

/-- An orthogonal diagonalization computes rank by counting its nonzero diagonal
entries. Horn–Johnson 2013, Section 4.1; all zero multiplicities are included.
-/
theorem rank_eq_card_nonzero_of_orthogonal_diagonalization {n : Type*}
    [Fintype n] [DecidableEq n] {T P : Matrix n n ℝ} (d : n → ℝ)
    (hPo : HasOrthonormalCols P) (hTd : T = P * Matrix.diagonal d * Pᵀ) :
    T.rank = Fintype.card {i // d i ≠ 0} := by
  have hP : Pᵀ * P = 1 := hPo
  have hPt : P * Pᵀ = 1 := mul_eq_one_comm.mp hP
  have hunit : IsUnit P := ⟨⟨P, Pᵀ, hPt, hP⟩, rfl⟩
  have hunitT : IsUnit Pᵀ := ⟨⟨Pᵀ, P, hP, hPt⟩, rfl⟩
  have hdet := (Matrix.isUnit_iff_isUnit_det P).mp hunit
  have hdetT := (Matrix.isUnit_iff_isUnit_det Pᵀ).mp hunitT
  rw [hTd, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdetT,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet, Matrix.rank_diagonal]

open scoped Matrix.Norms.L2Operator in
/-- The rank of a Kronecker product of symmetric real matrices is the product of
their ranks. Horn–Johnson 1991, Theorem 4.2.12, eigenvalue multiplicities.
-/
theorem rank_kronecker_of_isHermitian {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  rw [rank_eq_card_nonzero_of_orthogonal_diagonalization _
    (hasOrthonormalCols_kronecker (transpose_eigenvectorUnitary_mul_self hA)
      (transpose_eigenvectorUnitary_mul_self hB))
    (eq_eigenvectorUnitary_kronecker_mul_diagonal_mul_transpose hA hB),
    hA.rank_eq_card_non_zero_eigs, hB.rank_eq_card_non_zero_eigs]
  have e : {ij : m × n // hA.eigenvalues ij.1 * hB.eigenvalues ij.2 ≠ 0} ≃
      {i : m // hA.eigenvalues i ≠ 0} × {j : n // hB.eigenvalues j ≠ 0} :=
    (Equiv.subtypeEquivRight fun _ => mul_ne_zero_iff).trans
      (Equiv.subtypeProdEquivProd (α := m) (β := n)
        (p := fun i => hA.eigenvalues i ≠ 0) (q := fun j => hB.eigenvalues j ≠ 0))
  rw [Fintype.card_congr e, Fintype.card_prod]

/-- Kronecker rank multiplication for arbitrary finite rectangular real matrices.
Horn–Johnson 1991, Theorem 4.2.15. No rank, invertibility, or nonempty assumptions.
atlas: kronecker-spectral -/
theorem rank_kronecker {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n ℝ) (B : Matrix p q ℝ) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  have hA : (Aᵀ * A).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self A
  have hB : (Bᵀ * B).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self B
  rw [← Matrix.rank_transpose_mul_self (A ⊗ₖ B), ← Matrix.kroneckerMap_transpose,
    ← Matrix.mul_kronecker_mul, rank_kronecker_of_isHermitian hA hB,
    Matrix.rank_transpose_mul_self, Matrix.rank_transpose_mul_self]

end NLAlib
