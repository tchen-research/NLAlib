import NLAlib.Matrix.Inequalities.BlockOrderConsequences
/-!
# Complete PSD-block contraction toolkit

Weak and strict contraction, bilinear and relative-spectrum criteria, Schur
complements, equal-diagonal order, and inverse compression consequences.
Source: Horn--Johnson (2013), Section 7.7; atlas `psd-block-contraction`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Complete PSD-block contract, including singular diagonal blocks, all
strict versions with the correct nonzero-vector conditions, relative spectral
radius, zero-Schur Gram blocks, and inverse principal-submatrix inequalities.
All dimensions may be zero. Horn--Johnson (2013), Lemma 7.7.6 and
Theorems 7.7.7--7.7.16.
atlas: psd-block-contraction -/
theorem psd_block_contraction_characterizations
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {C : Matrix n n ℝ}
    (hA : A.PosSemidef) (hC : C.PosSemidef) :
    ((fromBlocks 1 B Bᵀ 1).PosSemidef ↔ specNorm B ≤ 1) ∧
    ((fromBlocks 1 B Bᵀ 1).PosDef ↔ specNorm B < 1) ∧
    ((fromBlocks A B Bᵀ C).PosSemidef ↔
      ∀ x y, (x ⬝ᵥ B *ᵥ y) ^ 2 ≤ quadForm A x * quadForm C y) ∧
    ((fromBlocks A B Bᵀ C).PosSemidef ↔
      ∀ x y, 2 * |x ⬝ᵥ B *ᵥ y| ≤ quadForm A x + quadForm C y) ∧
    ((fromBlocks A B Bᵀ C).PosSemidef ↔
      ∃ X : Matrix m n ℝ, specNorm X ≤ 1 ∧ B = CFC.sqrt A * X * CFC.sqrt C) ∧
    ((fromBlocks A B Bᵀ C).PosDef ↔ A.PosDef ∧ (C - Bᵀ * A⁻¹ * B).PosDef) ∧
    (A.PosDef → C.PosDef →
      ((fromBlocks A B Bᵀ C).PosSemidef ↔ spectralRadius ℝ (Bᵀ * A⁻¹ * B * C⁻¹) ≤ 1) ∧
      ((fromBlocks A B Bᵀ C).PosDef ↔ spectralRadius ℝ (Bᵀ * A⁻¹ * B * C⁻¹) < 1) ∧
      ((fromBlocks A B Bᵀ C).PosDef ↔
        ∃ X : Matrix m n ℝ, specNorm X < 1 ∧ B = CFC.sqrt A * X * CFC.sqrt C) ∧
      ((fromBlocks A B Bᵀ C).PosDef ↔
        ∀ x y, x ≠ 0 → y ≠ 0 → (x ⬝ᵥ B *ᵥ y) ^ 2 < quadForm A x * quadForm C y) ∧
      ((fromBlocks A B Bᵀ C).PosDef ↔
        ∀ x y, x ≠ 0 ∨ y ≠ 0 → 2 * |x ⬝ᵥ B *ᵥ y| < quadForm A x + quadForm C y)) ∧
    (∀ D : Matrix m m ℝ, D.PosSemidef → ((fromBlocks A D D A).PosSemidef ↔ D ≤ A)) ∧
    (A.PosDef → (fromBlocks A B Bᵀ (Bᵀ * A⁻¹ * B)).PosSemidef) ∧
    (A.PosDef → ∀ V : Matrix m n ℝ, HasOrthonormalCols V →
      (Vᵀ * A * V)⁻¹ ≤ Vᵀ * A⁻¹ * V) ∧
    (A.PosDef → ∀ f : n → m, Function.Injective f →
      (A.submatrix f f)⁻¹ ≤ A⁻¹.submatrix f f) := by
  have hbil := posSemidef_fromBlocks_iff_bilinear_tests (B := B) hA hC
  refine ⟨posSemidef_identity_fromBlocks_iff_specNorm_le_one B,
    posDef_identity_fromBlocks_iff_specNorm_lt_one B, hbil.1, hbil.2,
    posSemidef_fromBlocks_iff_exists_sqrt_contraction_factor hA hC,
    posDef_fromBlocks_iff_posDef_and_schur A B C, ?_,
    fun D hD => posSemidef_equal_diagonal_fromBlocks_iff_le hA hD,
    fun hAPD => fromBlocks_inverse_gram_posSemidef hAPD B,
    fun hAPD _ hV => inv_compression_le_compression_inv hAPD hV,
    fun hAPD f hf => inv_submatrix_le_submatrix_inv hAPD f hf⟩
  intro hAPD hCPD
  have hr := fromBlocks_positivity_iff_relative_spectralRadius (B := B) hAPD hCPD
  have hs := posDef_fromBlocks_iff_strict_bilinear_tests (B := B) hAPD hCPD
  exact ⟨hr.1, hr.2, posDef_fromBlocks_iff_exists_strict_sqrt_contraction_factor hAPD hCPD,
    hs.1, hs.2⟩

end NLAlib
