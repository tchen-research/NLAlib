import NLAlib.Matrix.Inequalities.BlockOrderConsequences
/-!
# Fischer's block determinant inequality

Schur complementation and PSD determinant monotonicity give the block bound.
Positive definite equality means the coupling vanishes. Singular PSD leading
blocks force singularity of the ambient block, so the weak result needs no
continuity argument. Source: Horn--Johnson (2013), Theorem 7.8.5;
atlas `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- A Gram compression of a positive definite matrix vanishes exactly when
its rectangular factor vanishes. Horn--Johnson (2013), Section 7.8;
helper for Fischer's equality case. -/
theorem transpose_mul_mul_eq_zero_iff_of_posDef {A : Matrix m m ℝ} (hA : A.PosDef)
    (B : Matrix m n ℝ) : Bᵀ * A * B = 0 ↔ B = 0 := by
  constructor
  · intro h
    ext i j
    let x : n → ℝ := Pi.single j 1
    have hq := congrArg (fun M : Matrix n n ℝ => x ⬝ᵥ M *ᵥ x) h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_transpose_mulVec] at hq
    have hzero : B *ᵥ x = 0 := by
      by_contra hn
      have hp := hA.dotProduct_mulVec_pos hn
      simp only [star_trivial] at hp
      rw [dotProduct_comm, Matrix.zero_mulVec, dotProduct_zero] at hq
      linarith
    simpa only [x, Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply, Matrix.zero_apply] using congrFun hzero i
  · rintro rfl
    simp

/-- Fischer's determinant inequality for arbitrary PSD real blocks, including
singular and empty diagonal blocks. Horn--Johnson (2013), Theorem 7.8.5
and its semidefinite extension.
atlas: hadamard-fischer-inequalities (partial) -/
theorem det_fromBlocks_le_mul_det_of_posSemidef
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hH : (fromBlocks A B Bᵀ C).PosSemidef) :
    (fromBlocks A B Bᵀ C).det ≤ A.det * C.det := by
  have hA : A.PosSemidef := hH.submatrix (Sum.inl : m → m ⊕ n)
  have hC : C.PosSemidef := hH.submatrix (Sum.inr : n → m ⊕ n)
  by_cases hAu : IsUnit A
  · have hAPD := hA.posDef_iff_isUnit.mpr hAu
    let : Invertible A := hAu.invertible
    have hS : (C - Bᵀ * A⁻¹ * B).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.PosDef.fromBlocks₁₁ B C hAPD).mp (by simpa using hH)
    have hCorr : (Bᵀ * A⁻¹ * B).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hAPD.inv.posSemidef.conjTranspose_mul_mul_same B
    have hSC : C - Bᵀ * A⁻¹ * B ≤ C := by
      simpa only [Matrix.le_iff, sub_sub_cancel] using hCorr
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    exact mul_le_mul_of_nonneg_left (det_le_det_of_posSemidef_le hS hSC) hA.det_nonneg
  · have hdetH : (fromBlocks A B Bᵀ C).det = 0 := by
      by_contra hne
      have hPD := hH.posDef_iff_det_ne_zero.mpr hne
      have hAPD : A.PosDef := hPD.submatrix
        (Sum.inl_injective : Function.Injective (Sum.inl : m → m ⊕ n))
      exact hAu hAPD.isUnit
    rw [hdetH]
    exact mul_nonneg hA.det_nonneg hC.det_nonneg

/-- Equality in Fischer's bound for a positive definite block matrix holds
exactly when its off-diagonal block is zero. Horn--Johnson (2013),
Theorem 7.8.5.
atlas: hadamard-fischer-inequalities (partial) -/
theorem det_fromBlocks_eq_mul_det_iff_of_posDef
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hH : (fromBlocks A B Bᵀ C).PosDef) :
    (fromBlocks A B Bᵀ C).det = A.det * C.det ↔ B = 0 := by
  have hA : A.PosDef := hH.submatrix
    (Sum.inl_injective : Function.Injective (Sum.inl : m → m ⊕ n))
  have hC : C.PosDef := hH.submatrix
    (Sum.inr_injective : Function.Injective (Sum.inr : n → m ⊕ n))
  let : Invertible A := hA.isUnit.invertible
  have hS := ((posDef_fromBlocks_iff_posDef_and_schur A B C).mp hH).2
  have hCorr : (Bᵀ * A⁻¹ * B).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.inv.posSemidef.conjTranspose_mul_mul_same B
  have hSC : C - Bᵀ * A⁻¹ * B ≤ C := by
    simpa only [Matrix.le_iff, sub_sub_cancel] using hCorr
  constructor
  · intro heq
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at heq
    have hdet := mul_left_cancel₀ hA.det_pos.ne' heq
    have he := (det_eq_iff_eq_of_posSemidef_le_posDef hC hS.posSemidef hSC).mp hdet
    have hz : Bᵀ * A⁻¹ * B = 0 := by
      have := congrArg (fun M : Matrix n n ℝ => C - M) he
      simpa only [sub_sub_cancel, sub_self] using this
    exact (transpose_mul_mul_eq_zero_iff_of_posDef hA.inv B).mp hz
  · rintro rfl
    simp [Matrix.det_fromBlocks_zero₂₁]

end NLAlib
