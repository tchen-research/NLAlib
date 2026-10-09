import TroppMatrixConcentration.Defs.Ch8Entropy

/-!
# ch8_jensen_reflection_algebra

Lean name: `TroppMatrixConcentration.ch8_jensen_reflection_algebra`.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder
open TroppMatrixConcentration

theorem TroppMatrixConcentration.ch8_jensen_reflection_algebra
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (K : Matrix ι κ ℂ) (hK : K.conjTranspose * K = 1)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    let U := Matrix.fromBlocks (1 - K * K.conjTranspose) K K.conjTranspose 0
    U.IsHermitian ∧ U * U = 1 ∧
      (U * Matrix.fromBlocks A 0 0 B * U).toBlocks₂₂ = K.conjTranspose * A * K := by
  let P := 1 - K * K.conjTranspose
  have hP : P.IsHermitian := by
    simp only [P, Matrix.IsHermitian, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hPK : P * K = 0 := by
    simp only [P, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hK, Matrix.mul_one, sub_self]
  have hKP : K.conjTranspose * P = 0 := by
    simp only [P, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hK, Matrix.one_mul, sub_self]
  have hPP : P * P + K * K.conjTranspose = 1 := by
    calc
      P * P + K * K.conjTranspose = P - (P * K) * K.conjTranspose + K * K.conjTranspose := by
        rw [show P * P = P * (1 - K * K.conjTranspose) from rfl,
          Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
      _ = 1 := by rw [hPK]; simp [P]
  dsimp only
  refine ⟨hP.fromBlocks rfl (Matrix.isHermitian_zero), ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply]
    change Matrix.fromBlocks (P * P + K * K.conjTranspose) (P * K + K * 0)
      (K.conjTranspose * P + 0 * K.conjTranspose) (K.conjTranspose * K + 0 * 0) = 1
    simp only [hPP, hPK, hKP, hK, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact Matrix.fromBlocks_one
  · simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂,
      Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]


