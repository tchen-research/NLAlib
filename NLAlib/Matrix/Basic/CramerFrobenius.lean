import NLAlib.Matrix.Basic.RowSubsetPseudoinverse
import NLAlib.Matrix.Subspaces.CoordinateFrames
import NLAlib.Matrix.Norms.Frobenius

/-! # Determinant-weighted squared Cramer solutions

Cramer's rule is applied to the actual inverse-selected-row solve. The
adapters identify this solve with the total ambient padded Moore–Penrose
inverse, and the squared determinant with its literal row-volume weight.
Source: Dereziński–Warmuth 2018, Theorem 8.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib

variable {𝕜 n d r : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

/-- Squared Cramer's rule for every right-hand-side column simultaneously.
The solve is the ordinary inverse of the displayed nonsingular matrix. -/
theorem norm_det_sq_mul_frobSq_inv_mul [Fintype r]
    (R : Matrix d d 𝕜) (hR : IsUnit R) (E : Matrix d r 𝕜) :
    ‖R.det‖ ^ 2 * frobSq (R⁻¹ * E) =
      ∑ i, ∑ j, ‖(R.updateCol i (fun a => E a j)).det‖ ^ 2 := by
  have he : R.det • (R⁻¹ * E) = fun i j => (R.updateCol i (fun a => E a j)).det := by
    ext i j
    have h := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer R (fun a => E a j)
      ((Matrix.isUnit_iff_isUnit_det _).mp hR)) i
    simpa only [Matrix.smul_mulVec, Pi.smul_apply, Matrix.smul_apply,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.cramer_apply] using h
  rw [← frobSq_smul_eq_norm_sq_mul, he]
  exact frobSq_eq_sum_norm_sq _

omit [Fintype n] [DecidableEq n] [DecidableEq d] in
/-- The fixed coordinate listing maps onto exactly its sized subset, as a finset. -/
theorem univ_map_sizedSubsetIndex (J : SizedSubset n d) :
    Finset.univ.map ⟨sizedSubsetIndex J, sizedSubsetIndex_injective J⟩ = J.val := by
  apply Finset.coe_injective
  simpa only [Finset.coe_map, Finset.coe_univ, Set.image_univ,
    Function.Embedding.coeFn_mk] using range_sizedSubsetIndex J

/-- At the full-column size the row-volume weight is precisely the squared
absolute determinant of the selected square restriction.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem rowSubsetVolume_sizedSubset (X : Matrix n d 𝕜) (J : SizedSubset n d) :
    rowSubsetVolume X J.val = ‖(X.submatrix (sizedSubsetIndex J) id).det‖ ^ 2 := by
  classical
  rw [rowSubsetVolume_eq_sum_minors, Finset.sum_eq_single J]
  · rw [if_pos (Finset.Subset.refl _)]
  · intro K _ hKJ
    rw [if_neg]
    intro hK
    exact hKJ (Subtype.ext (Finset.eq_of_subset_of_card_le hK (by rw [J.property, K.property])))
  · simp

/-- A size-width principal minor of a row Gram matrix equals the selected
column-Gram volume. This identity is valid for arbitrary data matrices, so
it includes singular restrictions without an orthonormality hypothesis.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem re_det_rowGram_sizedSubset_eq_rowSubsetVolume
    (X : Matrix n d 𝕜) (J : SizedSubset n d) :
    RCLike.re ((X * Xᴴ).submatrix (Subtype.val : J.val → n) Subtype.val).det =
      rowSubsetVolume X J.val := by
  let e : J.val ≃ d := Fintype.equivOfCardEq ((Fintype.card_coe J.val).trans J.property)
  let R := X.submatrix (sizedSubsetIndex J) id
  have hIndex : ((X * Xᴴ).submatrix (sizedSubsetIndex J) (sizedSubsetIndex J)).det =
      ((X * Xᴴ).submatrix (Subtype.val : J.val → n) Subtype.val).det := by
    change (((X * Xᴴ).submatrix (Subtype.val : J.val → n) Subtype.val).submatrix e.symm e.symm).det = _
    exact Matrix.det_submatrix_equiv_self e.symm _
  have hGram : (X * Xᴴ).submatrix (sizedSubsetIndex J) (sizedSubsetIndex J) = R * Rᴴ := by
    rw [Matrix.conjTranspose_submatrix]
    simpa only [R, Equiv.coe_refl] using
      (Matrix.submatrix_mul_equiv X Xᴴ (sizedSubsetIndex J) (Equiv.refl d) (sizedSubsetIndex J)).symm
  rw [← hIndex, hGram, Matrix.det_mul, Matrix.det_conjTranspose,
    rowSubsetVolume_sizedSubset, mul_comm, RCLike.star_def, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- A positive full-size row-volume weight makes the literal square row
restriction nonsingular. -/
theorem isUnit_submatrix_sizedSubset_of_rowSubsetVolume_pos
    (X : Matrix n d 𝕜) (J : SizedSubset n d) (hJ : 0 < rowSubsetVolume X J.val) :
    IsUnit (X.submatrix (sizedSubsetIndex J) id) := by
  rw [rowSubsetVolume_sizedSubset] at hJ
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hJ

/-- The actual padded row pseudoinverse solve equals the inverse-selected-row
solve at every supported full-size subset. -/
theorem rowSubsetPseudoinverse_sizedSubset_mul [Fintype r]
    (X : Matrix n d 𝕜) (J : SizedSubset n d) (hJ : 0 < rowSubsetVolume X J.val)
    (E : Matrix n r 𝕜) :
    rowSubsetPseudoinverse X J.val * E =
      (X.submatrix (sizedSubsetIndex J) id)⁻¹ * E.submatrix (sizedSubsetIndex J) id := by
  let e : d ↪ n := ⟨sizedSubsetIndex J, sizedSubsetIndex_injective J⟩
  have h := moorePenroseInverse_coordinateSelector_mul_mul X e
    (isUnit_submatrix_sizedSubset_of_rowSubsetVolume_pos X J hJ) E
  simpa only [rowSubsetPseudoinverse, e, univ_map_sizedSubsetIndex,
    Function.Embedding.coeFn_mk] using h

/-- The literal row-volume-weighted padded inverse solution has the Cramer
minor-square numerator on every supported full-size row subset. -/
theorem rowSubsetVolume_mul_frobSq_pseudoinverse_mul [Fintype r]
    (X : Matrix n d 𝕜) (J : SizedSubset n d) (hJ : 0 < rowSubsetVolume X J.val)
    (E : Matrix n r 𝕜) :
    rowSubsetVolume X J.val * frobSq (rowSubsetPseudoinverse X J.val * E) =
      ∑ i, ∑ j, ‖((X.updateCol i (fun a => E a j)).submatrix (sizedSubsetIndex J) id).det‖ ^ 2 := by
  rw [rowSubsetVolume_sizedSubset, rowSubsetPseudoinverse_sizedSubset_mul X J hJ E,
    norm_det_sq_mul_frobSq_inv_mul _ (isUnit_submatrix_sizedSubset_of_rowSubsetVolume_pos X J hJ)]
  rfl

/-- On every supported row subset, frame interpolation splits orthogonally
into the true projection residual and its solved coordinate residual. -/
theorem frobSq_rowSubset_interpolation_error [Fintype r]
    (Q : Matrix n d 𝕜) (hQ : HasOrthonormalCols Q) (S : Finset n)
    (hS : IsUnit (rowSubsetGram Q S)) (A : Matrix n r 𝕜) :
    frobSq (A - Q * (rowSubsetPseudoinverse Q S * A)) =
      frobSq (projResidual Q A) + frobSq (rowSubsetPseudoinverse Q S * projResidual Q A) := by
  have he : rowSubsetPseudoinverse Q S * projResidual Q A =
      rowSubsetPseudoinverse Q S * A - Qᴴ * A := by
    rw [projResidual, Matrix.mul_sub, ← Matrix.mul_assoc,
      rowSubsetPseudoinverse_mul_eq_one Q S hS, Matrix.one_mul]
  rw [frobSq_sub_mul_eq hQ, he, frobSq_sub_comm (rowSubsetPseudoinverse Q S * A)]

end NLAlib
