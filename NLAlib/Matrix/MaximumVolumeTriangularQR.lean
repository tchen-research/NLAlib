import NLAlib.Matrix.MaximumVolumeQR
import NLAlib.Matrix.Factorizations.Householder

/-!
# Upper-trapezoidal maximum-volume QR

Householder QR within the trailing row space makes the full factor upper
trapezoidal while preserving every maximum-volume guarantee.
Gu–Eisenstat 1996, Theorem 3.2; derivations §alg:rrqr.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Maximum-volume QR can have an upper-trapezoidal trailing block as well
as an invertible upper-triangular leading block, at every `k ≤ rank A`.
The orthogonal trailing row change preserves the interpolation entries and
the exact shared Frobenius budget. Gu–Eisenstat 1996, Theorem 3.2;
supports `rank-revealing-qr`. -/
theorem exists_maximum_volume_triangular_qr_blocks {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) (hk : k ≤ A.rank) :
    ∃ π : (Fin k ⊕ Fin (Fintype.card n - k)) ≃ n,
    ∃ Q : Matrix m (Fin k ⊕ Fin (Fintype.card m - k)) ℝ,
    ∃ R : Matrix (Fin k) (Fin k) ℝ,
    ∃ T : Matrix (Fin k) (Fin (Fintype.card n - k)) ℝ,
    ∃ D : Matrix (Fin (Fintype.card m - k)) (Fin (Fintype.card n - k)) ℝ,
      HasOrthonormalCols Q ∧ Q * Qᵀ = 1 ∧ IsUnit R ∧ R.IsUpperTriangular ∧
      IsUpperTrapezoidal D ∧
      A.submatrix id π = Q * Matrix.fromBlocks R (R * T) 0 D ∧
      (∀ i j, |T i j| ≤ 1) ∧
      frobSq T + frobSq R⁻¹ * frobSq D ≤ (k : ℝ) * (Fintype.card n - k) := by
  obtain ⟨π, Q, R, T, D, hQ, hQt, hR, hUpper, hFact, hEntry, hBudget⟩ :=
    exists_maximum_volume_qr_blocks A k hk
  let Z := householderQ D
  let D' := householderR D
  have hQR : IsFullQR D Z D' := isFullQR_householderQR D
  let K := Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 Z
  have hK : HasOrthonormalCols K := by
    change (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 Z)ᵀ *
      Matrix.fromBlocks 1 0 0 Z = 1
    simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, show Zᵀ * Z = 1 from hQR.orth, Matrix.fromBlocks_one]
  refine ⟨π, Q * K, R, T, D', hQ.mul hK, ?_, hR, hUpper, hQR.upper, ?_, hEntry, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc K Kᵀ Qᵀ,
      show K * Kᵀ = 1 from mul_eq_one_comm.mp hK, Matrix.one_mul, hQt]
  · rw [hFact, Matrix.mul_assoc]
    congr 1
    simp only [K, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, ← hQR.eq]
  · have hD : frobSq D = frobSq D' := by
      rw [hQR.eq, frobSq_mul_left_of_orthonormal hQR.orth]
    rwa [hD] at hBudget

end NLAlib
