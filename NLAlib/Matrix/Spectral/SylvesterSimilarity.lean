import NLAlib.Matrix.Spectral.SylvesterBlocks
/-!
# Commutants in disjoint-spectrum block coordinates

A similarity transports the disjoint-spectrum block commutant exactly.
The free diagonal blocks must commute with their respective primary blocks.
Source: Horn–Johnson (2013), Corollary 2.4.4.2.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- Simultaneous nonsingular conjugation preserves commutation.
Source: Horn–Johnson (2013), §1.3; matrix similarity algebra. -/
theorem commute_nonsing_inv_mul_mul_iff
    {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
    (A X S : Matrix n n K) (hS : IsUnit S) :
    Commute (S⁻¹ * A * S) (S⁻¹ * X * S) ↔ Commute A X := by
  let := hS.nonempty_invertible.some
  constructor
  · intro h
    change A * X = X * A
    have hh := congrArg (fun M : Matrix n n K => S * M * S⁻¹) h.eq
    simpa only [Matrix.mul_assoc, Matrix.mul_inv_cancel_left_of_invertible,
      Matrix.inv_mul_cancel_left_of_invertible, Matrix.mul_inv_of_invertible,
      Matrix.mul_one] using hh
  · intro h
    have hh := congrArg (fun M : Matrix n n K => S⁻¹ * M * S) h.eq
    change (S⁻¹ * A * S) * (S⁻¹ * X * S) = (S⁻¹ * X * S) * (S⁻¹ * A * S)
    simpa only [Matrix.mul_assoc, Matrix.mul_inv_cancel_left_of_invertible] using hh

/-- A conjugated block diagonal matrix with pairwise disjoint block spectra
has exactly the conjugates of block diagonal commuting matrices as its
commutant. Source: Horn–Johnson (2013), Corollary 2.4.4.2; diagonal blocks
are constrained to commute, correcting the unrestricted-block formulation.
atlas: sylvester-equation -/
theorem commute_similarity_blockDiagonal'_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {K : Type*} [Field K] [IsAlgClosed K]
    (A : ∀ i, Matrix (m i) (m i) K)
    (hdisj : Pairwise fun i j => Disjoint (spectrum K (A i)) (spectrum K (A j)))
    (S X : Matrix (Σ i, m i) (Σ i, m i) K) (hS : IsUnit S) :
    Commute (S * Matrix.blockDiagonal' A * S⁻¹) X ↔
      ∃ Y : ∀ i, Matrix (m i) (m i) K,
        X = S * Matrix.blockDiagonal' Y * S⁻¹ ∧ ∀ i, Commute (A i) (Y i) := by
  let := hS.nonempty_invertible.some
  rw [← commute_nonsing_inv_mul_mul_iff _ X S hS]
  have hconj : S⁻¹ * (S * Matrix.blockDiagonal' A * S⁻¹) * S = Matrix.blockDiagonal' A := by
    simp only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible,
      Matrix.inv_mul_of_invertible, Matrix.mul_one]
  rw [hconj, commute_blockDiagonal'_iff A hdisj]
  constructor
  · rintro ⟨Y, hY, hcomm⟩
    refine ⟨Y, ?_, hcomm⟩
    have h := congrArg (fun M => S * M * S⁻¹) hY
    simpa only [Matrix.mul_assoc, Matrix.mul_inv_cancel_left_of_invertible,
      Matrix.mul_inv_of_invertible, Matrix.mul_one] using h
  · rintro ⟨Y, hY, hcomm⟩
    refine ⟨Y, ?_, hcomm⟩
    rw [hY]
    simp only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible,
      Matrix.inv_mul_of_invertible, Matrix.mul_one]

end NLAlib
