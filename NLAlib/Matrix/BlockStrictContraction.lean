import NLAlib.Matrix.BlockQuadratic
import NLAlib.Matrix.StrictRelativeSpectrum
import NLAlib.Matrix.HaynsworthInertia

/-!
# Strict block contractions and relative spectral radius

For positive definite diagonal blocks, strict contraction is equivalent to
block positive definiteness. The actual relative spectral radius supplies
both the weak and strict criteria. Source: Horn--Johnson (2013),
Theorems 7.7.7--7.7.9; atlas `psd-block-contraction`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The identity-diagonal symmetric block is positive definite precisely
when the off-diagonal block has spectral norm strictly below one.
Horn--Johnson (2013), Lemma 7.7.6.
atlas: psd-block-contraction (partial) -/
theorem posDef_identity_fromBlocks_iff_specNorm_lt_one (X : Matrix m n ℝ) :
    (fromBlocks 1 X Xᵀ 1).PosDef ↔ specNorm X < 1 := by
  rw [posDef_fromBlocks_iff_posDef_schur Matrix.isHermitian_one isUnit_one,
    inv_one, Matrix.mul_one, and_iff_right Matrix.PosDef.one]
  have hG : (Xᵀ * X).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self X
  rw [posDef_one_sub_iff_specNorm_lt_one_of_posSemidef hG,
    ← specNorm_sq_eq_specNorm_transpose_mul_self]
  exact sq_lt_one_iff₀ (specNorm_nonneg X)

/-- For positive definite diagonal blocks, every square-root factorization
identifies positive definiteness with a strict contraction bound.
Horn--Johnson (2013), Theorem 7.7.7;
helper for strict PSD-block factorization. -/
theorem posDef_fromBlocks_iff_specNorm_lt_one_of_sqrt_factor
    {A : Matrix m m ℝ} {B X : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.PosDef) (hC : C.PosDef) (hB : B = CFC.sqrt A * X * CFC.sqrt C) :
    (fromBlocks A B Bᵀ C).PosDef ↔ specNorm X < 1 := by
  let D := fromBlocks (CFC.sqrt A) (0 : Matrix m n ℝ) (0 : Matrix n m ℝ) (CFC.sqrt C)
  have hSA : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hSC : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq
  have hD : IsUnit D := Matrix.isUnit_fromBlocks_zero₂₁.mpr
    ⟨(CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit,
      (CFC.isUnit_sqrt_iff C hC.posSemidef.nonneg).mpr hC.isUnit⟩
  have hBt : CFC.sqrt C * (Xᵀ * CFC.sqrt A) = Bᵀ := by
    rw [hB, Matrix.transpose_mul, Matrix.transpose_mul, hSA, hSC]
  have hfactor : D * fromBlocks 1 X Xᵀ 1 * star D = fromBlocks A B Bᵀ C := by
    simp only [D, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.fromBlocks_transpose, hSA, hSC, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add,
      CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg,
      CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg, ← hB, Matrix.mul_assoc, hBt]
  rw [← hfactor, hD.posDef_star_right_conjugate_iff,
    posDef_identity_fromBlocks_iff_specNorm_lt_one]

/-- A block with positive definite diagonal blocks is positive definite
exactly when it has a strict square-root contraction factorization.
Horn--Johnson (2013), Theorem 7.7.7.
atlas: psd-block-contraction (partial) -/
theorem posDef_fromBlocks_iff_exists_strict_sqrt_contraction_factor
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.PosDef) (hC : C.PosDef) :
    (fromBlocks A B Bᵀ C).PosDef ↔
      ∃ X : Matrix m n ℝ, specNorm X < 1 ∧ B = CFC.sqrt A * X * CFC.sqrt C := by
  constructor
  · intro hH
    obtain ⟨X, -, hX⟩ := exists_sqrt_contraction_factor_of_fromBlocks_posSemidef hH.posSemidef
    exact ⟨X, (posDef_fromBlocks_iff_specNorm_lt_one_of_sqrt_factor hA hC hX).mp hH, hX⟩
  · rintro ⟨X, hnorm, hX⟩
    exact (posDef_fromBlocks_iff_specNorm_lt_one_of_sqrt_factor hA hC hX).mpr hnorm

/-- Reversing a product of two real square matrices preserves its actual
real spectral radius, by the characteristic-polynomial identity.
Horn--Johnson (2013), Section 1.3; helper for block relative-radius tests. -/
theorem spectralRadius_mul_comm (A B : Matrix n n ℝ) :
    spectralRadius ℝ (A * B) = spectralRadius ℝ (B * A) := by
  have hs : spectrum ℝ (A * B) = spectrum ℝ (B * A) := by
    ext z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
      Matrix.charpoly_mul_comm]
  simp only [spectralRadius, hs]

/-- With positive definite diagonal blocks, relative spectral radius at
most one is equivalent to PSD block positivity; strict radius below one
is equivalent to positive definiteness. Empty blocks are included.
Horn--Johnson (2013), Theorems 7.7.7--7.7.9.
atlas: psd-block-contraction (partial) -/
theorem fromBlocks_positivity_iff_relative_spectralRadius
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.PosDef) (hC : C.PosDef) :
    ((fromBlocks A B Bᵀ C).PosSemidef ↔
      spectralRadius ℝ (Bᵀ * A⁻¹ * B * C⁻¹) ≤ 1) ∧
    ((fromBlocks A B Bᵀ C).PosDef ↔
      spectralRadius ℝ (Bᵀ * A⁻¹ * B * C⁻¹) < 1) := by
  let : Invertible A := hA.isUnit.invertible
  have hD : (Bᵀ * A⁻¹ * B).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.inv.posSemidef.conjTranspose_mul_mul_same B
  constructor
  · have hs := Matrix.PosDef.fromBlocks₁₁ B C hA
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hs
    rw [hs, ← Matrix.le_iff, le_iff_relative_spectralRadius_le_one hC hD,
      spectralRadius_mul_comm C⁻¹]
  · rw [posDef_fromBlocks_iff_posDef_schur hA.isHermitian hA.isUnit,
      and_iff_right hA, posDef_sub_iff_relative_spectralRadius_lt_one hC hD,
      spectralRadius_mul_comm C⁻¹]

end NLAlib
