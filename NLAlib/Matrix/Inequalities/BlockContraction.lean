import NLAlib.Matrix.Inequalities.RelativeSpectrum
import NLAlib.Matrix.Factorizations.PolarDecomposition
/-!
# Positive semidefinite blocks as contractive couplings

The Gram square root and rectangular polar factors give a contraction
between the two square roots, even for singular diagonal blocks.
Source: Horn--Johnson (2013), Section 7.7; atlas `psd-block-contraction`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The identity-diagonal block matrix is PSD exactly when its off-diagonal
block has spectral norm at most one. Includes rectangular and empty blocks.
Horn--Johnson (2013), Lemma 7.7.6.
atlas: psd-block-contraction (partial) -/
theorem posSemidef_identity_fromBlocks_iff_specNorm_le_one (X : Matrix m n ℝ) :
    (fromBlocks 1 X Xᵀ 1).PosSemidef ↔ specNorm X ≤ 1 := by
  let : Invertible (1 : Matrix m m ℝ) := invertibleOne
  have h := Matrix.PosDef.fromBlocks₁₁ X (1 : Matrix n n ℝ)
    (Matrix.PosDef.one : (1 : Matrix m m ℝ).PosDef)
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, inv_one, Matrix.mul_one] at h
  rw [h, ← Matrix.le_iff]
  simpa only [Matrix.transpose_transpose, specNorm_transpose] using
    mul_transpose_le_one_iff_specNorm_le_one Xᵀ

/-- A PSD block matrix has a contraction factor between its diagonal square
roots. This holds without invertibility or rank assumptions.
Horn--Johnson (2013), Theorem 7.7.9.
atlas: psd-block-contraction (partial) -/
theorem exists_sqrt_contraction_factor_of_fromBlocks_posSemidef
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hH : (fromBlocks A B Bᵀ C).PosSemidef) :
    ∃ X : Matrix m n ℝ, specNorm X ≤ 1 ∧ B = CFC.sqrt A * X * CFC.sqrt C := by
  let H := fromBlocks A B Bᵀ C
  let R := CFC.sqrt H
  have hRt : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg H).posSemidef.isHermitian.eq
  have hGram : Rᵀ * R = H := by rw [hRt]; exact CFC.sqrt_mul_sqrt_self H hH.nonneg
  let L := R.submatrix id Sum.inl
  let T := R.submatrix id Sum.inr
  have hLA : Lᵀ * L = A := by
    calc
      Lᵀ * L = (Rᵀ * R).submatrix Sum.inl Sum.inl :=
        Matrix.submatrix_mul_equiv Rᵀ R Sum.inl (Equiv.refl _) Sum.inl
      _ = A := by rw [hGram]; rfl
  have hTC : Tᵀ * T = C := by
    calc
      Tᵀ * T = (Rᵀ * R).submatrix Sum.inr Sum.inr :=
        Matrix.submatrix_mul_equiv Rᵀ R Sum.inr (Equiv.refl _) Sum.inr
      _ = C := by rw [hGram]; rfl
  have hLT : Lᵀ * T = B := by
    calc
      Lᵀ * T = (Rᵀ * R).submatrix Sum.inl Sum.inr :=
        Matrix.submatrix_mul_equiv Rᵀ R Sum.inl (Equiv.refl _) Sum.inr
      _ = B := by rw [hGram]; rfl
  obtain ⟨U, hU, hUL⟩ := exists_isometry_mul_sqrt_gram_eq L (by simp [Fintype.card_sum])
  obtain ⟨V, hV, hVT⟩ := exists_isometry_mul_sqrt_gram_eq T (by simp [Fintype.card_sum])
  rw [hLA] at hUL
  rw [hTC] at hVT
  refine ⟨Uᵀ * V, ?_, ?_⟩
  · calc
      specNorm (Uᵀ * V) ≤ specNorm Uᵀ * specNorm V := specNorm_mul_le _ _
      _ ≤ 1 := by
        rw [specNorm_transpose]
        exact (mul_le_mul (specNorm_le_one_of_orthonormal hU)
          (specNorm_le_one_of_orthonormal hV) (specNorm_nonneg V) zero_le_one).trans_eq (one_mul 1)
  · have hSA : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
    rw [← hLT, ← hUL, ← hVT, Matrix.transpose_mul, hSA]
    simp only [Matrix.mul_assoc]

/-- A contractive coupling of two PSD square roots gives a PSD block matrix.
Horn--Johnson (2013), Theorem 7.7.9.
atlas: psd-block-contraction (partial) -/
theorem fromBlocks_posSemidef_of_sqrt_contraction_factor
    {A : Matrix m m ℝ} {B X : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.PosSemidef) (hC : C.PosSemidef) (hX : specNorm X ≤ 1)
    (hB : B = CFC.sqrt A * X * CFC.sqrt C) :
    (fromBlocks A B Bᵀ C).PosSemidef := by
  let D := fromBlocks (CFC.sqrt A) (0 : Matrix m n ℝ) (0 : Matrix n m ℝ) (CFC.sqrt C)
  have hSA : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hSC : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq
  have h := ((posSemidef_identity_fromBlocks_iff_specNorm_le_one X).mpr hX).mul_mul_conjTranspose_same D
  have hBt : CFC.sqrt C * (Xᵀ * CFC.sqrt A) = Bᵀ := by
    rw [hB, Matrix.transpose_mul, Matrix.transpose_mul, hSA, hSC]
  simpa only [D, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.fromBlocks_transpose,
    hSA, hSC, Matrix.transpose_zero, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add,
    CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self C hC.nonneg,
    ← hB, Matrix.transpose_mul, hSA, hSC, Matrix.mul_assoc, hBt] using h

/-- PSD block positivity is equivalent to a contraction square-root
factorization, including singular diagonal blocks and empty dimensions.
Horn--Johnson (2013), Theorem 7.7.9.
atlas: psd-block-contraction (partial) -/
theorem posSemidef_fromBlocks_iff_exists_sqrt_contraction_factor
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.PosSemidef) (hC : C.PosSemidef) :
    (fromBlocks A B Bᵀ C).PosSemidef ↔
      ∃ X : Matrix m n ℝ, specNorm X ≤ 1 ∧ B = CFC.sqrt A * X * CFC.sqrt C := by
  constructor
  · exact exists_sqrt_contraction_factor_of_fromBlocks_posSemidef
  · rintro ⟨X, hX, hB⟩
    exact fromBlocks_posSemidef_of_sqrt_contraction_factor hA hC hX hB

end NLAlib
