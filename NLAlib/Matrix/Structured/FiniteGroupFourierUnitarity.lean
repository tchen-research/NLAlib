import NLAlib.Matrix.Structured.FiniteGroupFourierCompleteness
import NLAlib.Matrix.Structured.FiniteGroupFourierOrthogonality
import NLAlib.Matrix.Subspaces.OrthogonalProducts

/-! # The actual finite group Fourier basis and unitary transform

Schur orthogonality and irreducible-family completeness prove a genuine
orthonormal basis. Its dimension formula and two-sided Fourier inversion are
derived conclusions.
Source: finite Schur route for `gaussian-cayley-fourier-block-law`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset Representation
open scoped Matrix ComplexInnerProductSpace
namespace NLAlib

universe u v
variable {G : Type u} [Group G] [Fintype G]
  {P : Type v} {D : P → Type u} [∀ p, Fintype (D p)] [∀ p, DecidableEq (D p)]
  [∀ p, Nonempty (D p)] [Fintype P] [DecidableEq P]
  (ρ : ∀ p, Representation ℂ G (D p → ℂ))

/-- Completeness makes the actual Fourier columns span the entire regular space. -/
theorem columnSpace_finiteGroupFourierMatrix (hcomplete : IsCompleteIrreducibleFamily ρ) :
    columnSpace (finiteGroupFourierMatrix ρ) = ⊤ := by
  apply top_unique
  rw [← finiteGroupCoefficientSpan_eq_top ρ hcomplete]
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  let c : ℂ := Real.sqrt ((Fintype.card (D t.1) : ℝ) / Fintype.card G)
  have hc : c ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact ne_of_gt (Real.sqrt_pos.mpr (div_pos
      (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast Fintype.card_pos)))
  have hcol : (WithLp.toLp 2 ((finiteGroupFourierMatrix ρ).col t) :
      EuclideanSpace ℂ G) ∈ columnSpace (finiteGroupFourierMatrix ρ) := by
    rw [columnSpace_eq_span_columns]
    exact Submodule.subset_span ⟨t, rfl⟩
  have he : (WithLp.toLp 2 ((finiteGroupFourierMatrix ρ).col t) :
      EuclideanSpace ℂ G) = c • finiteGroupCoefficient ρ t := by
    ext g
    rfl
  rw [he] at hcol
  have hh := Submodule.smul_mem (columnSpace (finiteGroupFourierMatrix ρ)) c⁻¹ hcol
  change finiteGroupCoefficient ρ t ∈ columnSpace (finiteGroupFourierMatrix ρ)
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

variable [∀ p, Representation.IsIrreducible (ρ p)]

/-- The actual normalized matrix coefficients form a complete orthonormal basis
of the finite regular space; completeness and orthogonality are proved, not inputs.
atlas: gaussian-cayley-fourier-block-law (partial) -/
def finiteGroupFourierBasis
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (hcomplete : IsCompleteIrreducibleFamily ρ) :
    OrthonormalBasis (FiniteGroupFourierIndex D) ℂ (EuclideanSpace ℂ G) :=
  OrthonormalBasis.mk (finiteGroupFourierMatrix_hasOrthonormalCols ρ hu hne).orthonormal
    (by rw [← columnSpace_eq_span_columns, columnSpace_finiteGroupFourierMatrix ρ hcomplete])

/-- Evaluation of the derived Fourier basis is exactly the normalized coefficient
column, with multiplicity and representation coordinates in the declared order. -/
@[simp] theorem finiteGroupFourierBasis_apply
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (hcomplete : IsCompleteIrreducibleFamily ρ) (t : FiniteGroupFourierIndex D) :
    finiteGroupFourierBasis ρ hu hne hcomplete t =
      WithLp.toLp 2 ((finiteGroupFourierMatrix ρ).col t) := by
  simp [finiteGroupFourierBasis]

/-- The sum-of-squared-dimensions formula follows from the actual Fourier basis.
Source: finite Schur orthogonality and completeness.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem sum_sq_card_irreducible_dimensions
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (hcomplete : IsCompleteIrreducibleFamily ρ) :
    (∑ p, Fintype.card (D p) ^ 2) = Fintype.card G := by
  have hh := Module.finrank_eq_card_basis (finiteGroupFourierBasis ρ hu hne hcomplete).toBasis
  simpa [FiniteGroupFourierIndex, Fintype.card_sigma, Fintype.card_prod, pow_two] using hh.symm

/-- A complete irreducible family of a finite group has a nonempty index type.
This supplies the instance required to write finite maxima over its blocks. -/
theorem nonempty_index_of_completeIrreducibleFamily
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (hcomplete : IsCompleteIrreducibleFamily ρ) : Nonempty P := by
  by_contra hP
  haveI : IsEmpty P := ⟨fun p => hP ⟨p⟩⟩
  have hh := sum_sq_card_irreducible_dimensions ρ hu hne hcomplete
  have hN : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  exact hN (by simpa using hh.symm)

/-- Completeness supplies the second Fourier Gram identity, so the actual
rectangular-index Fourier matrix is unitary in both directions.
atlas: gaussian-cayley-fourier-block-law (partial) -/
theorem finiteGroupFourierMatrix_mul_conjTranspose
    [DecidableEq G]
    (hu : ∀ p g, LinearMap.toMatrix' (ρ p g) ∈ Matrix.unitaryGroup (D p) ℂ)
    (hne : ∀ p q, p ≠ q → IsEmpty (Representation.Equiv (ρ p) (ρ q)))
    (hcomplete : IsCompleteIrreducibleFamily ρ) :
    finiteGroupFourierMatrix ρ * (finiteGroupFourierMatrix ρ)ᴴ = 1 := by
  let B := finiteGroupFourierBasis ρ hu hne hcomplete
  ext g h
  have hh := congrArg (fun x : EuclideanSpace ℂ G => x g)
    (B.sum_repr' (EuclideanSpace.single h (1 : ℂ)))
  simpa [B, finiteGroupFourierBasis_apply, PiLp.inner_apply, Matrix.col,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, PiLp.toLp_apply, EuclideanSpace.single,
    mul_comm] using hh

end NLAlib
