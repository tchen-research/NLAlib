/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import NLAlib.ForMathlib.Combinatorics.OrderedSubsetSums

/-!
# Ordered histories and principal minors

Simultaneously reindexing rows and columns preserves a principal determinant;
repeated indices give a zero determinant. Consequently the sum over all
length-`k` histories is `k!` times the sum of size-`k` principal minors.
This counting identity needs no positivity hypothesis.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib

variable {R n ι : Type*} [CommRing R] [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι]

omit [Fintype n] in
/-- An injective ordered selection has the same determinant as its image
principal block. The signs of the row and column permutations cancel. -/
theorem det_submatrix_eq_det_image_of_injective (A : Matrix n n R)
    (h : ι → n) (hh : Function.Injective h) :
    (A.submatrix h h).det =
      (A.submatrix (Subtype.val : (Finset.univ.image h) → n) Subtype.val).det := by
  let e : ι ≃ (Finset.univ.image h) := Equiv.ofBijective
    (fun i => ⟨h i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) (by
      constructor
      · intro i j hij
        exact hh (congrArg Subtype.val hij)
      · intro x
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.2
        exact ⟨i, Subtype.ext hi⟩)
  exact (Matrix.det_submatrix_equiv_self e
    (A.submatrix (Subtype.val : (Finset.univ.image h) → n) Subtype.val))

omit [Fintype n] [DecidableEq n] in
/-- Repeated indices force a selected principal determinant to vanish. -/
theorem det_submatrix_eq_zero_of_not_injective (A : Matrix n n R)
    (h : ι → n) (hh : ¬Function.Injective h) : (A.submatrix h h).det = 0 := by
  rw [Function.Injective] at hh
  push Not at hh
  obtain ⟨i, j, hij, hne⟩ := hh
  apply Matrix.det_zero_of_row_eq hne
  funext l
  change A (h i) (h l) = A (h j) (h l)
  rw [hij]

/-- Summing over every length-`k` ordered history counts each principal minor
`k!` times. Noninjective histories contribute zero, and all endpoint dimensions
are included. -/
theorem sum_det_submatrix_eq_factorial_mul_sum_principalMinors (A : Matrix n n R) (k : ℕ) :
    (∑ h : Fin k → n, (A.submatrix h h).det) =
      (k.factorial : R) * ∑ S ∈ (Finset.univ : Finset n).powersetCard k,
        (A.submatrix (Subtype.val : S → n) Subtype.val).det := by
  classical
  calc
    _ = ∑ h : Fin k → n, if Function.Injective h then
        (A.submatrix (Subtype.val : (Finset.univ.image h) → n) Subtype.val).det else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      split_ifs with hh
      · exact det_submatrix_eq_det_image_of_injective A h hh
      · exact det_submatrix_eq_zero_of_not_injective A h hh
    _ = _ := by
      simpa only [nsmul_eq_mul] using Finset.sum_injective_image_eq_factorial_nsmul
        (fun S : Finset n => (A.submatrix (Subtype.val : S → n) Subtype.val).det) k

end NLAlib
