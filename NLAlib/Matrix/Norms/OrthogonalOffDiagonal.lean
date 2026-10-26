import NLAlib.Matrix.Norms.BlockDiagonalBounds
import NLAlib.Matrix.Norms.SpectralNormBounds
import NLAlib.Matrix.Basic.SchurRank
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Norms and rank of an off-diagonal coupling between orthogonal subspaces

For orthonormal frames `V,U` with `VᴴU=0`, the Hermitian matrix
`UZVᴴ+VZᴴUᴴ` has spectral norm `‖Z‖₂`, squared Frobenius norm `2‖Z‖F²`,
and rank `2 rank Z`. All empty shapes are included. These finite identities
provide residual certificates for projected matrix equations.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 n k l : Type*} [RCLike 𝕜] [Fintype n] [Fintype k] [Fintype l]
  [DecidableEq n] [DecidableEq k] [DecidableEq l]

omit [Fintype n] [DecidableEq n] in
/-- An adjoint pair of off-diagonal blocks has the original spectral norm, including
zero-width blocks. -/
theorem specNorm_fromBlocks_conjTranspose (Z : Matrix l k 𝕜) :
    specNorm (Matrix.fromBlocks 0 Zᴴ Z 0) = specNorm Z := by
  apply le_antisymm
  · simpa only [specNorm_conjTranspose, max_self] using
      specNorm_fromBlocks_offDiagonal_le Zᴴ Z
  · apply specNorm_le_of_sum_norm_sq_mulVec_le (specNorm_nonneg _)
    intro x
    have h := sum_norm_sq_mulVec_le_specNorm_sq (Matrix.fromBlocks 0 Zᴴ Z 0)
      (Sum.elim x (0 : l → 𝕜))
    simpa only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.mulVec_zero,
      Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type,
      Pi.zero_apply, ← Pi.zero_def, Matrix.mulVec_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, zero_add, add_zero] using h

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq l] in
/-- An adjoint off-diagonal pair has twice the rectangular block's rank. -/
theorem rank_fromBlocks_conjTranspose (Z : Matrix l k 𝕜) :
    (Matrix.fromBlocks 0 Zᴴ Z 0).rank = 2 * Z.rank := by
  have he : (Matrix.fromBlocks 0 Zᴴ Z 0).reindex (Equiv.refl (k ⊕ l))
      (Equiv.sumComm k l) = Matrix.fromBlocks Zᴴ 0 0 Z := by
    ext (i | i) (j | j) <;> rfl
  rw [← Matrix.rank_reindex (Equiv.refl (k ⊕ l)) (Equiv.sumComm k l), he,
    rank_fromBlocks_zero_zero_eq, Matrix.rank_conjTranspose]
  omega

omit [DecidableEq n] in
/-- Isometric embedding on both sides preserves rank. -/
theorem rank_mul_mul_conjTranspose_of_hasOrthonormalCols {V : Matrix n k 𝕜}
    (hV : HasOrthonormalCols V) (D : Matrix k k 𝕜) :
    (V * D * Vᴴ).rank = D.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have he : Vᴴ * (V * D * Vᴴ) * V = D := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV.conjTranspose_mul_self,
        Matrix.one_mul, Matrix.mul_one]
    calc D.rank = (Vᴴ * (V * D * Vᴴ) * V).rank := congrArg Matrix.rank he.symm
         _ ≤ (Vᴴ * (V * D * Vᴴ)).rank := Matrix.rank_mul_le_left _ _
         _ ≤ (V * D * Vᴴ).rank := Matrix.rank_mul_le_right _ _

omit [Fintype k] [Fintype l] [DecidableEq n] in
/-- Joining orthogonal orthonormal frames gives an orthonormal frame. -/
theorem hasOrthonormalCols_fromCols_of_orthogonal {V : Matrix n k 𝕜} {U : Matrix n l 𝕜}
    (hV : HasOrthonormalCols V) (hU : HasOrthonormalCols U) (hVU : Vᴴ * U = 0) :
    HasOrthonormalCols (Matrix.fromCols V U) := by
  have hUV : Uᴴ * V = 0 := by
    have h := congrArg Matrix.conjTranspose hVU
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using h
  change (Matrix.fromCols V U)ᴴ * Matrix.fromCols V U = 1
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols, hV.conjTranspose_mul_self,
    hU.conjTranspose_mul_self, hVU, hUV, Matrix.fromBlocks_one]

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq l] in
/-- The off-diagonal coupling is the isometric embedding of its small Hermitian block. -/
theorem orthogonalCoupling_eq_fromCols (V : Matrix n k 𝕜) (U : Matrix n l 𝕜)
    (Z : Matrix l k 𝕜) :
    U * Z * Vᴴ + V * Zᴴ * Uᴴ = Matrix.fromCols V U *
      Matrix.fromBlocks 0 Zᴴ Z 0 * (Matrix.fromCols V U)ᴴ := by
  simp only [Matrix.fromCols_mul_fromBlocks, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows, Matrix.mul_zero, zero_add, add_zero]

/-- All three exact invariants of a coupling between orthogonal subspaces.
Zero-width and zero-rank couplings are retained. -/
theorem norms_and_rank_orthogonalCoupling {V : Matrix n k 𝕜} {U : Matrix n l 𝕜}
    (hV : HasOrthonormalCols V) (hU : HasOrthonormalCols U) (hVU : Vᴴ * U = 0)
    (Z : Matrix l k 𝕜) :
    frobSq (U * Z * Vᴴ + V * Zᴴ * Uᴴ) = 2 * frobSq Z ∧
      specNorm (U * Z * Vᴴ + V * Zᴴ * Uᴴ) = specNorm Z ∧
      (U * Z * Vᴴ + V * Zᴴ * Uᴴ).rank = 2 * Z.rank := by
  have hW := hasOrthonormalCols_fromCols_of_orthogonal hV hU hVU
  rw [orthogonalCoupling_eq_fromCols]
  refine ⟨?_, ?_, ?_⟩
  · rw [frobSq_mul_right_of_orthonormal hW.conjTranspose_mul_self,
      frobSq_mul_left_of_orthonormal hW.conjTranspose_mul_self,
      frobSq_fromBlocks, frobSq_conjTranspose]
    simp only [frobSq_zero]
    ring
  · rw [specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hW,
      specNorm_mul_left_of_hasOrthonormalCols hW, specNorm_fromBlocks_conjTranspose]
  · rw [rank_mul_mul_conjTranspose_of_hasOrthonormalCols hW, rank_fromBlocks_conjTranspose]

end NLAlib
