import NLAlib.Matrix.Structured.FiniteGroupCayleyFourier
import NLAlib.Matrix.Structured.FiniteGroupFourierNormalization
import NLAlib.Matrix.Norms.DependentBlockDiagonal

/-! # Exact norm of finite group Cayley convolution

The actual unitary Fourier decomposition and the exact norm of dependent
repeated blocks give a pointwise maximum, with the source normalization.
Source: `gaussian-cayley-fourier-block-law`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset Representation
open scoped Matrix Kronecker
namespace NLAlib

universe u v
variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
  {P : Type v} {D : P → Type u} [∀ p, Fintype (D p)] [∀ p, DecidableEq (D p)]
  [∀ p, Nonempty (D p)] [Fintype P] [DecidableEq P] [Nonempty P]
  (ρ : ∀ p, Representation ℂ G (D p → ℂ)) [∀ p, Representation.IsIrreducible (ρ p)]

/-- The spectral norm of every actual Cayley matrix is exactly the maximum
of its unnormalized representation-block spectral norms.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem specNorm_finiteGroupCayleyMatrix_eq_max_blocks
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (hcomplete : IsCompleteIrreducibleFamily ρ) (z : G → ℂ) :
    specNorm (finiteGroupCayleyMatrix z) =
      Finset.univ.sup' Finset.univ_nonempty (fun p =>
        specNorm (finiteGroupRepresentationBlock ρ z p)) := by
  have hU := finiteGroupFourierMatrix_hasOrthonormalCols ρ hu hne
  rw [finiteGroupCayleyMatrix_eq_fourier_mul_blocks_mul_conjTranspose ρ hu hne hcomplete,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hU,
    specNorm_mul_left_of_hasOrthonormalCols hU,
    finiteGroupFourierBlocks, specNorm_blockDiagonal'_one_kronecker_eq_max]

open scoped Matrix.Norms.L2Operator in
/-- The normalized actual blocks have exactly the `sqrt(N/d)` scaling required
by the source circular complex Gaussian convention. -/
theorem specNorm_finiteGroupRepresentationBlock_eq_normalized
    (z : G → ℂ) (p : P) :
    specNorm (finiteGroupRepresentationBlock ρ z p) =
      Real.sqrt ((Fintype.card G : ℝ) / Fintype.card (D p)) *
        specNorm (finiteGroupNormalizedBlock ρ z p) := by
  rw [← sqrt_card_div_smul_finiteGroupNormalizedBlock ρ z p,
    specNorm_eq_norm, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    ← specNorm_eq_norm]

/-- The exact Cayley spectral norm is the finite maximum of the normalized
block norms with their representation dimensions, pointwise for every input.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem specNorm_finiteGroupCayleyMatrix_eq_max_normalized_blocks
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (hcomplete : IsCompleteIrreducibleFamily ρ) (z : G → ℂ) :
    specNorm (finiteGroupCayleyMatrix z) =
      Finset.univ.sup' Finset.univ_nonempty (fun p =>
        Real.sqrt ((Fintype.card G : ℝ) / Fintype.card (D p)) *
          specNorm (finiteGroupNormalizedBlock ρ z p)) := by
  rw [specNorm_finiteGroupCayleyMatrix_eq_max_blocks ρ hu hne hcomplete]
  simp_rw [specNorm_finiteGroupRepresentationBlock_eq_normalized ρ]

/-- Pointwise Fourier reconstruction written in terms of the actual normalized
blocks and the source factors, retaining all multiplicities.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem finiteGroupCayleyMatrix_eq_fourier_normalized_blocks
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (hcomplete : IsCompleteIrreducibleFamily ρ) (z : G → ℂ) :
    finiteGroupCayleyMatrix z = finiteGroupFourierMatrix ρ *
      Matrix.blockDiagonal' (fun p => (1 : Matrix (D p) (D p) ℂ) ⊗ₖ
        (Real.sqrt ((Fintype.card G : ℝ) / Fintype.card (D p)) •
          finiteGroupNormalizedBlock ρ z p)) * (finiteGroupFourierMatrix ρ)ᴴ := by
  simp_rw [sqrt_card_div_smul_finiteGroupNormalizedBlock]
  exact finiteGroupCayleyMatrix_eq_fourier_mul_blocks_mul_conjTranspose ρ hu hne hcomplete z

end NLAlib
