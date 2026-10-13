import NLAlib.Matrix.Inequalities.BlockStrictContraction
import NLAlib.Matrix.Functions.HermitianCalculus
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Consequences of positive block matrices

Equal-diagonal blocks characterize Loewner domination. Zero Schur complements
give Gram blocks and inverse compression bounds, including inverse principal
submatrix inequalities. Source: Horn--Johnson (2013), Theorems 7.7.11--7.7.16;
atlas `psd-block-contraction`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- For PSD real matrices, a symmetric equal-diagonal block matrix is PSD
exactly when its off-diagonal block is below its diagonal block.
Horn--Johnson (2013), Theorem 7.7.11.
atlas: psd-block-contraction (partial) -/
theorem posSemidef_equal_diagonal_fromBlocks_iff_le
    {A B : Matrix m m ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (fromBlocks A B B A).PosSemidef ↔ B ≤ A := by
  have hBt : Bᵀ = B := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.isHermitian.eq
  constructor
  · intro hH
    have hH' : (fromBlocks A B Bᵀ A).PosSemidef := by simpa only [hBt] using hH
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hA.isHermitian.sub hB.isHermitian)
    intro x
    have h := hH'.dotProduct_mulVec_nonneg (Sum.elim x (-x))
    simp only [star_trivial] at h ⊢
    change 0 ≤ quadForm (fromBlocks A B Bᵀ A) (Sum.elim x (-x)) at h
    rw [quadForm_fromBlocks] at h
    simp only [quadForm_def, star_trivial, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg,
      Matrix.sub_mulVec, dotProduct_sub] at h ⊢
    linarith
  · intro hBA
    have hEq : (fromBlocks B B B B).PosSemidef := by
      have h := hB.mul_mul_conjTranspose_same (fromRows (1 : Matrix m m ℝ) (1 : Matrix m m ℝ))
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_fromRows,
        Matrix.transpose_one, Matrix.fromRows_mul, Matrix.one_mul,
        Matrix.fromRows_mul_fromCols] at h
      simpa only [Matrix.mul_one] using h
    have hDiag := posSemidef_fromBlocks_diag (Matrix.le_iff.mp hBA) (Matrix.le_iff.mp hBA)
    convert hEq.add hDiag using 1
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]

omit [DecidableEq n] in
/-- The block with lower-right corner `Xᵀ A⁻¹ X` is PSD when `A` is positive
definite, since its Schur complement is zero.
Horn--Johnson (2013), Theorem 7.7.16.
atlas: psd-block-contraction (partial) -/
theorem fromBlocks_inverse_gram_posSemidef {A : Matrix m m ℝ}
    (hA : A.PosDef) (X : Matrix m n ℝ) :
    (fromBlocks A X Xᵀ (Xᵀ * A⁻¹ * X)).PosSemidef := by
  let : Invertible A := hA.isUnit.invertible
  have h := Matrix.PosDef.fromBlocks₁₁ X (Xᵀ * A⁻¹ * X) hA
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, sub_self] at h
  exact h.mpr Matrix.PosSemidef.zero

/-- Inverse compression dominates the inverse of a compression to an
orthonormal frame. Empty frames are included; no frame completion is needed.
Horn--Johnson (2013), Theorem 7.7.15 and its compression form.
atlas: psd-block-contraction (partial) -/
theorem inv_compression_le_compression_inv {A : Matrix m m ℝ} {V : Matrix m n ℝ}
    (hA : A.PosDef) (hV : HasOrthonormalCols V) :
    (Vᵀ * A * V)⁻¹ ≤ Vᵀ * A⁻¹ * V := by
  change Vᵀ * V = 1 at hV
  have hVi : Function.Injective V.mulVec := by
    intro x y hxy
    have h := congrArg (fun v => Vᵀ *ᵥ v) hxy
    simpa only [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec] using h
  have hAV : (Vᵀ * A * V).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.conjTranspose_mul_mul_same hVi
  have hH : (fromBlocks A 1 1 A⁻¹).PosSemidef := by
    simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using
      fromBlocks_inverse_gram_posSemidef hA (1 : Matrix m m ℝ)
  let D := fromBlocks V (0 : Matrix m n ℝ) (0 : Matrix m n ℝ) V
  have h := hH.conjTranspose_mul_mul_same D
  have hcomp : (fromBlocks (Vᵀ * A * V) 1 1 (Vᵀ * A⁻¹ * V)).PosSemidef := by
    simpa only [D, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.fromBlocks_transpose,
      Matrix.transpose_zero, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, hV] using h
  let : Invertible (Vᵀ * A * V) := hAV.isUnit.invertible
  have hs := (Matrix.PosDef.fromBlocks₁₁ (1 : Matrix n n ℝ) (Vᵀ * A⁻¹ * V) hAV).mp
    (by simpa only [Matrix.conjTranspose_one] using hcomp)
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, ← Matrix.le_iff] using hs

/-- Every principal submatrix of the inverse of a positive definite matrix
dominates the inverse of that principal submatrix, for every injective
coordinate selection including the empty one.
Horn--Johnson (2013), Theorem 7.7.15.
atlas: psd-block-contraction (partial) -/
theorem inv_submatrix_le_submatrix_inv {A : Matrix m m ℝ} (hA : A.PosDef)
    (f : n → m) (hf : Function.Injective f) :
    (A.submatrix f f)⁻¹ ≤ A⁻¹.submatrix f f := by
  let V := (1 : Matrix m m ℝ).submatrix id f
  have hc (M : Matrix m m ℝ) : Vᵀ * M * V = M.submatrix f f := by
    rw [show Vᵀ = (1 : Matrix m m ℝ).submatrix f id by
      simp only [V, Matrix.transpose_submatrix, Matrix.transpose_one]]
    have hl : (1 : Matrix m m ℝ).submatrix f id * M = M.submatrix f id := by
      simpa using Matrix.one_submatrix_mul f (Equiv.refl m) M
    rw [hl]
    simpa [V] using Matrix.mul_submatrix_one (Equiv.refl m) f (M.submatrix f id)
  have hV : HasOrthonormalCols V := by
    change Vᵀ * V = 1
    have hh := hc (1 : Matrix m m ℝ)
    simpa only [Matrix.mul_one, Matrix.submatrix_one f hf] using hh
  simpa only [hc] using inv_compression_le_compression_inv hA hV

end NLAlib
