import NLAlib.Matrix.FischerDeterminant

/-!
# Overlapping principal blocks after a common Schur elimination

Eliminating the common leading block reduces the overlapping-minor
inequality to Fischer, and its equality to a vanishing off-diagonal Schur
block. Source: Horn--Johnson (2013), Theorem 7.8.9;
supports `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]
  [DecidableEq ι] [DecidableEq m] [DecidableEq n]

/-- Two principal blocks that share a common leading block satisfy the
overlapping determinant inequality. Equality is exactly vanishing of the
cross Schur block after eliminating the intersection. Empty intersections
and empty exclusive blocks are included. Horn--Johnson (2013), Theorem 7.8.9;
helper for the principal-index Koteljanski inequality. -/
theorem det_overlapping_blocks_le_and_eq_iff
    (P : Matrix ι ι ℝ) (U : Matrix ι m ℝ) (V : Matrix ι n ℝ)
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hH : (fromBlocks P (fromCols U V) (fromCols U V)ᵀ (fromBlocks A B Bᵀ C)).PosDef) :
    (fromBlocks P (fromCols U V) (fromCols U V)ᵀ (fromBlocks A B Bᵀ C)).det * P.det ≤
      (fromBlocks P U Uᵀ A).det * (fromBlocks P V Vᵀ C).det ∧
    ((fromBlocks P (fromCols U V) (fromCols U V)ᵀ (fromBlocks A B Bᵀ C)).det * P.det =
      (fromBlocks P U Uᵀ A).det * (fromBlocks P V Vᵀ C).det ↔
      B - Uᵀ * P⁻¹ * V = 0) := by
  have hP : P.PosDef := hH.submatrix
    (Sum.inl_injective : Function.Injective (Sum.inl : ι → ι ⊕ (m ⊕ n)))
  let : Invertible P := hP.isUnit.invertible
  have hPt : P⁻¹ᵀ = P⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.inv.isHermitian.eq
  let SA := A - Uᵀ * P⁻¹ * U
  let SB := B - Uᵀ * P⁻¹ * V
  let SC := C - Vᵀ * P⁻¹ * V
  have hSchur : fromBlocks A B Bᵀ C - (fromCols U V)ᵀ * P⁻¹ * fromCols U V =
      fromBlocks SA SB SBᵀ SC := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    ext i j
    cases i <;> cases j <;>
      simp [SA, SB, SC, Matrix.fromBlocks, Matrix.transpose_sub, Matrix.transpose_mul,
        hPt, Matrix.mul_assoc]
  have hSPD : (fromBlocks SA SB SBᵀ SC).PosDef := by
    rw [← hSchur]
    exact ((posDef_fromBlocks_iff_posDef_and_schur P (fromCols U V) (fromBlocks A B Bᵀ C)).mp hH).2
  have hdet : (fromBlocks P (fromCols U V) (fromCols U V)ᵀ (fromBlocks A B Bᵀ C)).det =
      P.det * (fromBlocks SA SB SBᵀ SC).det := by
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, hSchur]
  have hdetA : (fromBlocks P U Uᵀ A).det = P.det * SA.det := by
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have hdetC : (fromBlocks P V Vᵀ C).det = P.det * SC.det := by
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  rw [hdet, hdetA, hdetC]
  constructor
  · have h := mul_le_mul_of_nonneg_left (det_fromBlocks_le_mul_det_of_posSemidef hSPD.posSemidef)
      (sq_nonneg P.det)
    nlinarith
  · have heq : (P.det * (fromBlocks SA SB SBᵀ SC).det * P.det =
        P.det * SA.det * (P.det * SC.det)) ↔ (fromBlocks SA SB SBᵀ SC).det = SA.det * SC.det := by
      constructor
      · intro h
        apply mul_left_cancel₀ (pow_ne_zero 2 hP.det_pos.ne')
        nlinarith
      · intro h
        rw [h]
        ring
    rw [heq, det_fromBlocks_eq_mul_det_iff_of_posDef hSPD]

end NLAlib
