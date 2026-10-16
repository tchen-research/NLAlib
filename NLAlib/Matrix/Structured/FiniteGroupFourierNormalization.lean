import NLAlib.Matrix.Structured.FiniteGroupFourierBasic

/-! # Normalized finite group Fourier blocks

The actual normalized blocks agree entrywise with the coefficient transform,
and unnormalizing has exactly the source factor `sqrt(N/d)`.
Source: `gaussian-cayley-fourier-block-law`, circular convention `E|z|² = 2`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset Representation
open scoped Matrix
namespace NLAlib

universe u v
variable {G : Type u} [Group G] [Fintype G]
  {P : Type v} {D : P → Type u} [∀ p, Fintype (D p)] [∀ p, DecidableEq (D p)]

/-- The actual Fourier block normalized to the input circular Gaussian entry
convention, by the scalar `sqrt(d/N)`. -/
def finiteGroupNormalizedBlock (ρ : ∀ p, Representation ℂ G (D p → ℂ))
    (z : G → ℂ) (p : P) : Matrix (D p) (D p) ℂ :=
  Real.sqrt ((Fintype.card (D p) : ℝ) / Fintype.card G) •
    finiteGroupRepresentationBlock ρ z p

/-- Concatenating the normalized actual block entries is exactly multiplication
by the concrete normalized coefficient transform. -/
theorem finiteGroupNormalizedBlock_apply
    (ρ : ∀ p, Representation ℂ G (D p → ℂ)) (z : G → ℂ)
    (p : P) (a b : D p) :
    finiteGroupNormalizedBlock ρ z p a b =
      (finiteGroupCoefficientTransform ρ *ᵥ z) ⟨p, a, b⟩ := by
  simp only [finiteGroupNormalizedBlock, finiteGroupRepresentationBlock,
    Matrix.smul_apply, Matrix.sum_apply, RCLike.real_smul_eq_coe_mul,
    smul_eq_mul, Matrix.mulVec, dotProduct, finiteGroupCoefficientTransform,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  simp only [mul_assoc, mul_left_comm, mul_comm]
  rfl

/-- Removing the normalization gives the exact `sqrt(N/d)` source factor,
including arbitrary singular or zero actual blocks. -/
theorem sqrt_card_div_smul_finiteGroupNormalizedBlock
    [∀ p, Nonempty (D p)] (ρ : ∀ p, Representation ℂ G (D p → ℂ))
    (z : G → ℂ) (p : P) :
    Real.sqrt ((Fintype.card G : ℝ) / Fintype.card (D p)) •
      finiteGroupNormalizedBlock ρ z p = finiteGroupRepresentationBlock ρ z p := by
  have hN : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : (Fintype.card (D p) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [finiteGroupNormalizedBlock, smul_smul, ← Real.sqrt_mul (by positivity)]
  have hh : ((Fintype.card G : ℝ) / Fintype.card (D p)) *
      ((Fintype.card (D p) : ℝ) / Fintype.card G) = 1 := by field_simp
  rw [hh, Real.sqrt_one, one_smul]

end NLAlib
