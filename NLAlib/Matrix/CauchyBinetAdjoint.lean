import NLAlib.Matrix.CauchyBinet
import Mathlib.Analysis.Complex.Basic

/-!
# Identity and adjoint compounds, and complex Gram minors

These are direct corollaries of the existing arbitrary-ring Cauchy--Binet
identity. The fixed subset enumerations are reused under the adjoint.
Source: Horn--Johnson (2013), Sections 0.8.1 and 0.8.7;
derivations Section alg:cauchy-binet.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib

/-- The chosen enumeration of a sized subset is injective.
Horn--Johnson (2013), Section 0.8.7; compound-matrix coordinate helper. -/
theorem sizedSubsetIndex_injective {n r : Type*} [Fintype r]
    (S : SizedSubset n r) : Function.Injective (sizedSubsetIndex S) := by
  exact Subtype.val_injective.comp (Equiv.injective _)

/-- The chosen enumeration ranges over exactly its sized subset.
Horn--Johnson (2013), Section 0.8.7; compound-matrix coordinate helper. -/
theorem range_sizedSubsetIndex {n r : Type*} [Fintype r]
    (S : SizedSubset n r) : Set.range (sizedSubsetIndex S) = (S.val : Set n) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (Fintype.equivOfCardEq
      ((Fintype.card_coe S.val).trans S.property)).symm i |>.property
  · intro hx
    let e : S.val ≃ r := Fintype.equivOfCardEq ((Fintype.card_coe S.val).trans S.property)
    refine ⟨e ⟨x, hx⟩, ?_⟩
    simp only [sizedSubsetIndex, e, Equiv.symm_apply_apply]

/-- The compound of the identity is the identity at every minor size,
including the unique empty minor and impossible-size empty compounds.
Source: Horn--Johnson (2013), Section 0.8.7.
atlas: cauchy-binet (partial)
-/
theorem compoundMatrix_one {n r R : Type*} [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r] [CommRing R] :
    compoundMatrix r (1 : Matrix n n R) = 1 := by
  classical
  ext S T
  by_cases hST : S = T
  · subst T
    simp only [compoundMatrix, Matrix.submatrix_one _ (sizedSubsetIndex_injective S),
      Matrix.det_one, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hST]
    have hnsub : ¬ S.val ⊆ T.val := by
      intro hsub
      exact hST (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [S.property, T.property])))
    obtain ⟨x, hxS, hxT⟩ := Finset.not_subset.mp hnsub
    obtain ⟨i, hi⟩ := (range_sizedSubsetIndex S ▸ hxS : x ∈ Set.range (sizedSubsetIndex S))
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    change (1 : Matrix n n R) (sizedSubsetIndex S i) (sizedSubsetIndex T j) = 0
    apply Matrix.one_apply_ne
    intro h
    apply hxT
    rw [← hi, h]
    exact (range_sizedSubsetIndex T ▸ Set.mem_range_self j : sizedSubsetIndex T j ∈ (T.val : Set n))

/-- Compounds commute with conjugate transpose over every commutative star
ring, using exactly the same fixed row and column enumerations.
Source: Horn--Johnson (2013), Section 0.8.7.
atlas: cauchy-binet (partial)
-/
theorem compoundMatrix_conjTranspose {m n r R : Type*}
    [Fintype r] [DecidableEq r] [CommRing R] [StarRing R]
    (A : Matrix m n R) :
    compoundMatrix r Aᴴ = (compoundMatrix r A)ᴴ := by
  ext S T
  change (Aᴴ.submatrix (sizedSubsetIndex S) (sizedSubsetIndex T)).det =
    star ((A.submatrix (sizedSubsetIndex T) (sizedSubsetIndex S)).det)
  rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]

/-- The complex column-Gram determinant is the sum of squared absolute
values of all full-column minors. Too few rows, singular matrices and
empty rows or columns need no separate hypotheses.
Source: Horn--Johnson (2013), Section 0.8.1.
atlas: cauchy-binet (partial)
-/
theorem det_conjTranspose_mul_self_eq_sum_norm_sq {m r : Type*}
    [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
    (A : Matrix m r ℂ) :
    (Aᴴ * A).det = ∑ S : SizedSubset m r,
      (‖(A.submatrix (sizedSubsetIndex S) id).det‖ ^ 2 : ℝ) := by
  rw [det_mul_eq_sum_det_submatrix_mul_det_submatrix, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]
  simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using
    (Complex.normSq_eq_conj_mul_self (z := (A.submatrix (sizedSubsetIndex S) id).det)).symm

end NLAlib
