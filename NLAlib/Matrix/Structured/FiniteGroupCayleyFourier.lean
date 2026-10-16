import NLAlib.Matrix.Structured.FiniteGroupFourierUnitarity

/-! # Pointwise Fourier decomposition of finite Cayley matrices

The actual regular representation is intertwined with a direct sum in which
the first coordinate is multiplicity and the second is the representation
coordinate. The identity holds for every coefficient vector before probability
is introduced.
Source: finite Schur route for `gaussian-cayley-fourier-block-law`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset Representation
open scoped Matrix Kronecker
namespace NLAlib

universe u v
variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
  {P : Type v} {D : P → Type u} [∀ p, Fintype (D p)] [∀ p, DecidableEq (D p)]
  [Fintype P] [DecidableEq P]
  (ρ : ∀ p, Representation ℂ G (D p → ℂ))

/-- Actual left translation permutes the rows of any matrix of functions. -/
theorem finiteGroupRegularMatrix_mul_apply {r : Type*} (A : Matrix G r ℂ)
    (h g : G) (t : r) :
    (finiteGroupRegularMatrix h * A) g t = A (h⁻¹ * g) t := by
  change (LinearMap.toMatrix' (finiteGroupLeftRegularRepresentation h) *ᵥ
    (fun k => A k t)) g = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

/-- Right multiplication by the Fourier block diagonal preserves the
multiplicity coordinate and applies the representation block to the second. -/
theorem mul_finiteGroupFourierBlocks_apply {r : Type*}
    (A : Matrix r (FiniteGroupFourierIndex D) ℂ) (z : G → ℂ)
    (g : r) (p : P) (a b : D p) :
    (A * finiteGroupFourierBlocks ρ z) g ⟨p, a, b⟩ =
      ∑ c : D p, A g ⟨p, a, c⟩ * finiteGroupRepresentationBlock ρ z p c b := by
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single p]
  · simp [finiteGroupFourierBlocks, Matrix.blockDiagonal'_apply_eq,
      Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
      mul_ite, ite_mul]
  · intro q _ hqp
    apply Finset.sum_eq_zero
    intro t _
    rw [finiteGroupFourierBlocks, Matrix.blockDiagonal'_apply_ne _ _ _ hqp, mul_zero]
  · simp

/-- The actual normalized Fourier coefficients obey the representation
intertwining identity, with the first index fixed as multiplicity. -/
theorem finiteGroupFourierMatrix_translate (h g : G) (p : P) (a b : D p) :
    finiteGroupFourierMatrix ρ (h⁻¹ * g) ⟨p, a, b⟩ =
      ∑ c : D p, finiteGroupFourierMatrix ρ g ⟨p, a, c⟩ *
        LinearMap.toMatrix' (ρ p h) c b := by
  simp only [finiteGroupFourierMatrix, _root_.mul_inv_rev, inv_inv, map_mul,
    LinearMap.toMatrix'_mul, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

/-- Every complex coefficient vector satisfies the exact finite Fourier
intertwining identity for its actual Cayley convolution matrix.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem finiteGroupCayleyMatrix_mul_fourier (z : G → ℂ) :
    finiteGroupCayleyMatrix z * finiteGroupFourierMatrix ρ =
      finiteGroupFourierMatrix ρ * finiteGroupFourierBlocks ρ z := by
  ext g ⟨p, a, b⟩
  rw [mul_finiteGroupFourierBlocks_apply]
  simp only [finiteGroupCayleyMatrix, Matrix.sum_mul, Matrix.smul_mul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    finiteGroupRegularMatrix_mul_apply, finiteGroupFourierMatrix_translate,
    finiteGroupRepresentationBlock, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro c _
  ring

variable [∀ p, Nonempty (D p)] [∀ p, Representation.IsIrreducible (ρ p)]

/-- Fourier conjugation block-diagonalizes every actual Cayley matrix, with
each irreducible block repeated its dimension times.
Source: finite Schur orthogonality and completeness, equation W12.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem finiteGroupFourier_conjTranspose_mul_cayley_mul_fourier
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (z : G → ℂ) :
    (finiteGroupFourierMatrix ρ)ᴴ * finiteGroupCayleyMatrix z *
      finiteGroupFourierMatrix ρ = finiteGroupFourierBlocks ρ z := by
  rw [Matrix.mul_assoc, finiteGroupCayleyMatrix_mul_fourier, ← Matrix.mul_assoc,
    (finiteGroupFourierMatrix_hasOrthonormalCols ρ hu hne).conjTranspose_mul_self,
    Matrix.one_mul]

/-- Pointwise reconstruction of the actual Cayley matrix from the representation
blocks and the Fourier matrix derived from the complete irreducible family.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem finiteGroupCayleyMatrix_eq_fourier_mul_blocks_mul_conjTranspose
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (hcomplete : IsCompleteIrreducibleFamily ρ) (z : G → ℂ) :
    finiteGroupCayleyMatrix z = finiteGroupFourierMatrix ρ *
      finiteGroupFourierBlocks ρ z * (finiteGroupFourierMatrix ρ)ᴴ := by
  calc
    _ = finiteGroupCayleyMatrix z *
        (finiteGroupFourierMatrix ρ * (finiteGroupFourierMatrix ρ)ᴴ) := by
      rw [finiteGroupFourierMatrix_mul_conjTranspose ρ hu hne hcomplete, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, finiteGroupCayleyMatrix_mul_fourier]

end NLAlib
