import NLAlib.Matrix.Spectral.SimultaneousTriangularization
/-!
# Paired spectra of commuting sums and products

The same common Schur coordinates pair the characteristic roots of two
commuting matrices so their sums and products give the full characteristic
root lists of the matrix sum and product.
Source: Horn–Johnson (2013), Corollaries 2.4.8.5–2.4.8.6.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

/-- The diagonal of the product of two upper triangular matrices is the
pointwise product of their diagonals. Source: Horn–Johnson (2013), §0.7;
helper for the commuting spectral sum and product formulas. -/
theorem mul_apply_self_eq_mul_of_isUpperTriangular
    {n K : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [Semiring K]
    {A B : Matrix n n K} (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

/-- Commuting matrices have complete characteristic eigenvalue lists in
paired orders for which the sum and product spectra are the corresponding
scalar sums and products. Source: Horn–Johnson (2013), Corollaries
2.4.8.5–2.4.8.6; multiplicities, repeated eigenvalues and empty shapes are
retained by the four characteristic-polynomial factorizations.
atlas: simultaneous-diagonalization (partial) -/
theorem exists_paired_charpoly_factors_add_mul_of_commute
    {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ} (hAB : Commute A B) :
    ∃ a b : n → ℂ,
      A.charpoly = ∏ i, (X - C (a i)) ∧ B.charpoly = ∏ i, (X - C (b i)) ∧
      (A + B).charpoly = ∏ i, (X - C (a i + b i)) ∧
      (A * B).charpoly = ∏ i, (X - C (a i * b i)) := by
  classical
  let F : Bool → Matrix n n ℂ := fun j => if j then A else B
  have hF : Pairwise fun i j => Commute (F i) (F j) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hAB.symm
    · exact hAB
    · exact (hij rfl).elim
  let e : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  obtain ⟨U, T, hT⟩ := exists_simultaneous_unitary_schur_triangularization F hF e
  obtain ⟨hA, hTA, hcharA⟩ := hT true
  obtain ⟨hB, hTB, hcharB⟩ := hT false
  let : LinearOrder n := LinearOrder.lift' e.symm e.symm.injective
  have hTA' : (T true).IsUpperTriangular := hTA
  have hTB' : (T false).IsUpperTriangular := hTB
  have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hchar (M : Matrix n n ℂ) :
      ((U : Matrix n n ℂ) * M * (U : Matrix n n ℂ)ᴴ).charpoly = M.charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUt, Matrix.one_mul]
  change A = _ at hA
  change B = _ at hB
  refine ⟨fun i => T true i i, fun i => T false i i, hcharA, hcharB, ?_, ?_⟩
  · have hsum : A + B = (U : Matrix n n ℂ) * (T true + T false) * (U : Matrix n n ℂ)ᴴ := by
      rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
    rw [hsum, hchar, Matrix.charpoly_of_isUpperTriangular _ (hTA'.add hTB')]
    rfl
  · have hprod : A * B = (U : Matrix n n ℂ) * (T true * T false) * (U : Matrix n n ℂ)ᴴ := by
      rw [hA, hB]
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),
        hUt, Matrix.one_mul]
    rw [hprod, hchar, Matrix.charpoly_of_isUpperTriangular _ (hTA'.mul hTB')]
    simp only [mul_apply_self_eq_mul_of_isUpperTriangular hTA' hTB']

end NLAlib
