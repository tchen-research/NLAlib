import NLAlib.Matrix.SVD
import NLAlib.Matrix.PolynomialIntertwining

/-!
# Singular values of odd rectangular Gram powers

The power-scheme matrix `(A Aᵀ)^q A` has singular values `σ_j(A)^(2q+1)`.
The identity includes all zero padding and zero matrix dimensions.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n : ℕ}

/-- An SVD diagonalizes every odd rectangular Gram power.
Source: HMT (2011), §10.4; manuscript `sa:expected-power`. -/
theorem IsSVD.gram_pow_mul_eq {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (h : IsSVD A U V) (q : ℕ) :
    (A * Aᵀ) ^ q * A = U *
      (rectDiag (fun j => singularValues A j ^ (2 * q + 1)) : Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
  let D : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.diagonal fun i => singularValues A i ^ 2
  have hM : (A * Aᵀ) * U = U * D := by
    rw [h.mul_transpose_self]
    simp only [Matrix.mul_assoc]
    rw [h.transpose_mul_left, Matrix.mul_one]
  have hp := pow_mul_eq_mul_pow_of_mul_eq hM q
  have hdiag : D ^ q * (rectDiag (singularValues A) : Matrix (Fin m) (Fin n) ℝ) =
      rectDiag (fun j => singularValues A j ^ (2 * q + 1)) := by
    dsimp only [D]
    rw [Matrix.diagonal_pow]
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [Pi.pow_apply, rectDiag_apply]
    split_ifs with hij
    · simp only [← pow_mul, ← pow_succ]
    · simp
  conv_lhs => arg 2; rw [h.eq]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hp, Matrix.mul_assoc U, hdiag]

/-- Odd rectangular Gram powers raise every singular value to the corresponding odd
power. Source: HMT (2011), §10.4; manuscript `sa:expected-power-theorem`.
The identity is zero-indexed and includes zero padding beyond the finite list. -/
theorem singularValues_gram_pow_mul (A : Matrix (Fin m) (Fin n) ℝ) (q j : ℕ) :
    singularValues ((A * Aᵀ) ^ q * A) j = singularValues A j ^ (2 * q + 1) := by
  by_cases hj : j < min m n
  · obtain ⟨U, V, h⟩ := exists_isSVD A
    exact singularValues_eq_of_eq_mul_rectDiag_mul h.transpose_mul_left
      h.transpose_mul_right (fun i => pow_nonneg (singularValues_nonneg A i) _)
      (fun a b hab => pow_le_pow_left₀ (singularValues_nonneg A b)
        (singularValues_antitone A hab) _) (h.gram_pow_mul_eq q) hj
  · rw [singularValues_eq_zero_of_min_le _ (not_lt.mp hj),
      singularValues_eq_zero_of_min_le _ (not_lt.mp hj), zero_pow (by omega)]

/-- Odd rectangular Gram powers preserve rank, including rank zero.
Source: HMT (2011), §10.4; manuscript `sa:expected-power`, exact-width branch. -/
theorem rank_gram_pow_mul (A : Matrix (Fin m) (Fin n) ℝ) (q : ℕ) :
    ((A * Aᵀ) ^ q * A).rank = A.rank := by
  rw [rank_eq_card_singularValues_ne_zero, rank_eq_card_singularValues_ne_zero]
  congr 1
  apply Finset.filter_congr
  intro j _
  rw [singularValues_gram_pow_mul]
  exact pow_ne_zero_iff (by omega)

end NLAlib
