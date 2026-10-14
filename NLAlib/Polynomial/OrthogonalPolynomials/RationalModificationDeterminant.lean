import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationConstraints
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.GroupTheory.Perm.Fin

/-!
# The actual rational-modification numerator determinant

The monomial constraint matrix has a bordered polynomial determinant. Its
normalization is proved nonzero, and the normalized quotient is the canonical
modified monic polynomial. Both the convenient last-row form and the source's
first-row form are exposed, with their exact permutation sign.
Source: focused rational-modification reroute, Section 4 (CU4)--(CU5).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Polynomial Finset Matrix

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- The actual constraint determinant with the polynomial row last and the
leading monomial column last. The source's first-row form differs by `(-1)^d`. -/
def rationalModificationBorderMatrix (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ) :
    Matrix (Fin (u.natDegree + n) ⊕ Fin 1) (Fin (u.natDegree + n) ⊕ Fin 1) 𝕜[X] :=
  fromBlocks ((rationalModificationConstraintMatrix T u n).map C)
    (fun i _ => C (rationalModificationLeadingConstraints T u n i))
    (fun _ j => X ^ j.val) (fun _ _ => X ^ (u.natDegree + n))

/-- Multiplying the bordered determinant by the original leading coefficient
gives the normalization determinant times the actually computed numerator. -/
theorem C_leadingCoeff_mul_det_rationalModificationBorderMatrix
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    C u.leadingCoeff * (rationalModificationBorderMatrix T u n).det =
      C (rationalModificationConstraintMatrix T u n).det * rationalModificationNumerator T u n := by
  let M := rationalModificationConstraintMatrix T u n
  have hdet : M.det ≠ 0 := det_rationalModificationConstraintMatrix_ne_zero T hu hn
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  let : Invertible (M.map C) :=
    { invOf := (M⁻¹).map C
      invOf_mul_self := by rw [← Matrix.map_mul, M.nonsing_inv_mul hunit]; simp
      mul_invOf_self := by rw [← Matrix.map_mul, M.mul_nonsing_inv hunit]; simp }
  rw [rationalModificationBorderMatrix, det_fromBlocks₁₁,
    det_eq_elem_of_subsingleton _ (0 : Fin 1)]
  have hmap : (M.map C).det = C M.det := (RingHom.map_det C M).symm
  rw [hmap, mul_left_comm]
  congr 1
  change C u.leadingCoeff * (X^(u.natDegree+n) - ∑ j : Fin (u.natDegree+n),
      (∑ i : Fin (u.natDegree+n), X^i.val * C (M⁻¹ i j)) *
        C (rationalModificationLeadingConstraints T u n j)) =
    rationalModificationNumerator T u n
  rw [rationalModificationNumerator]
  simp only [sum_mul]
  rw [sum_comm, mul_sub, mul_sum]
  rw [← C_mul_X_pow_eq_monomial]
  rw [sub_eq_add_neg]
  congr 1
  rw [neg_eq_iff_eq_neg, ← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  rw [rationalModificationCoefficients]
  change C u.leadingCoeff * (∑ j : Fin (u.natDegree+n),
      X^i.val * C (M⁻¹ i j) * C (rationalModificationLeadingConstraints T u n j)) =
    -monomial i.val ((M⁻¹ *ᵥ
      (fun j => -u.leadingCoeff * rationalModificationLeadingConstraints T u n j)) i)
  simp only [mulVec, dotProduct, ← C_mul_X_pow_eq_monomial,
    mul_neg, neg_mul, sum_neg_distrib, neg_neg, map_sum, map_mul, map_neg]
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  ring

/-- The bordered determinant is the actual computed numerator times the exact
scalar normalization, including the empty lower system. -/
theorem det_rationalModificationBorderMatrix_eq
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    (rationalModificationBorderMatrix T u n).det =
      ((rationalModificationConstraintMatrix T u n).det / u.leadingCoeff) •
        rationalModificationNumerator T u n := by
  have h := C_leadingCoeff_mul_det_rationalModificationBorderMatrix T hu hn
  have hlc : u.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hu
  have huC : C u.leadingCoeff ≠ (0 : 𝕜[X]) := C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hu)
  apply mul_left_cancel₀ huC
  rw [h, smul_eq_C_mul, ← mul_assoc, ← map_mul]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hlc]

/-- The bordered determinant's leading coefficient is exactly the finite
constraint matrix determinant. -/
@[simp] theorem coeff_det_rationalModificationBorderMatrix_self
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    (rationalModificationBorderMatrix T u n).det.coeff (u.natDegree + n) =
      (rationalModificationConstraintMatrix T u n).det := by
  rw [det_rationalModificationBorderMatrix_eq T hu hn, coeff_smul,
    coeff_rationalModificationNumerator_self, smul_eq_mul,
    div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hu)]

/-- The source's actual determinant matrix: polynomial row `1,X,...,X^d`
first, followed by the `d` native constraints, with `d=degree u+n`. -/
def rationalModificationFirstRowMatrix (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ) :
    Matrix (Fin (u.natDegree + n + 1)) (Fin (u.natDegree + n + 1)) 𝕜[X] :=
  fun i j => if hi : i.val = 0 then X ^ j.val else
    C (rationalModificationConstraint T u n
      ⟨i.val - 1, by have := i.isLt; omega⟩ (X ^ j.val))

/-- The first row is exactly the increasing monomial row from the source. -/
@[simp] theorem rationalModificationFirstRowMatrix_zero_apply
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ) (j : Fin (u.natDegree + n + 1)) :
    rationalModificationFirstRowMatrix T u n 0 j = X ^ j.val := by
  simp [rationalModificationFirstRowMatrix]

/-- Each row after the first is exactly the corresponding native constraint. -/
@[simp] theorem rationalModificationFirstRowMatrix_succ_apply
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ)
    (i : Fin (u.natDegree + n)) (j : Fin (u.natDegree + n + 1)) :
    rationalModificationFirstRowMatrix T u n i.succ j =
      C (rationalModificationConstraint T u n i (X ^ j.val)) := by
  simp [rationalModificationFirstRowMatrix]

private theorem rationalModificationBorderMatrix_lastRow
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ)
    (j : Fin (u.natDegree + n + 1)) :
    rationalModificationBorderMatrix T u n (Sum.inr 0) (finSumFinEquiv.symm j) = X ^ j.val := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [rationalModificationBorderMatrix]
  · simp [rationalModificationBorderMatrix]

private theorem rationalModificationBorderMatrix_constraintRow
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ)
    (i : Fin (u.natDegree + n)) (j : Fin (u.natDegree + n + 1)) :
    rationalModificationBorderMatrix T u n (Sum.inl i) (finSumFinEquiv.symm j) =
      C (rationalModificationConstraint T u n i (X ^ j.val)) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [rationalModificationBorderMatrix, rationalModificationLeadingConstraints]
  · simp [rationalModificationBorderMatrix, rationalModificationConstraintMatrix]

/-- Moving the polynomial row from last to first gives exactly the source sign
`(-1)^d`, including the one-by-one empty-constraint case. -/
theorem det_rationalModificationFirstRowMatrix_eq
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ) :
    (rationalModificationFirstRowMatrix T u n).det =
      (-1 : 𝕜[X])^(u.natDegree + n) * (rationalModificationBorderMatrix T u n).det := by
  let B := (rationalModificationBorderMatrix T u n).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  have hrows : rationalModificationFirstRowMatrix T u n =
      B.submatrix (Fin.last (u.natDegree+n)).cycleRange.symm id := by
    funext i j
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [rationalModificationFirstRowMatrix_zero_apply, Matrix.submatrix_apply,
        id_eq, B, Fin.cycleRange_symm_zero, finSumFinEquiv_symm_last]
      exact (rationalModificationBorderMatrix_lastRow T u n j).symm
    · simp only [rationalModificationFirstRowMatrix_succ_apply, Matrix.submatrix_apply,
        id_eq, B, Fin.cycleRange_symm_succ, Fin.succAbove_last,
        finSumFinEquiv_symm_apply_castSucc]
      exact (rationalModificationBorderMatrix_constraintRow T u n k j).symm
  rw [hrows, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
  simp

/-- The exact source normalization coefficient is `(-1)^d det M`. -/
theorem coeff_det_rationalModificationFirstRowMatrix_self
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    (rationalModificationFirstRowMatrix T u n).det.coeff (u.natDegree + n) =
      (-1 : 𝕜)^(u.natDegree + n) * (rationalModificationConstraintMatrix T u n).det := by
  rw [det_rationalModificationFirstRowMatrix_eq,
    show (-1 : 𝕜[X])^(u.natDegree + n) = C ((-1 : 𝕜)^(u.natDegree + n)) by simp,
    coeff_C_mul, coeff_det_rationalModificationBorderMatrix_self T hu hn]

/-- The actual first-row normalization minor is nonzero, proved from finite
modified nondegeneracy. Source: focused rational-modification reroute (CU4)--(CU5).
atlas: christoffel-uvarov-modification (partial) -/
theorem coeff_det_rationalModificationFirstRowMatrix_self_ne_zero
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    (rationalModificationFirstRowMatrix T u n).det.coeff (u.natDegree + n) ≠ 0 := by
  rw [coeff_det_rationalModificationFirstRowMatrix_self T hu hn]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (det_rationalModificationConstraintMatrix_ne_zero T hu hn)

/-- Normalizing the actual first-row determinant computes exactly the finite
source numerator. Its normalization coefficient has already been proved nonzero. -/
theorem rationalModificationNumerator_eq_smul_det_firstRowMatrix
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    rationalModificationNumerator T u n =
      (u.leadingCoeff / (rationalModificationFirstRowMatrix T u n).det.coeff (u.natDegree+n)) •
        (rationalModificationFirstRowMatrix T u n).det := by
  have hlc : u.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hu
  have hdet := det_rationalModificationConstraintMatrix_ne_zero T hu hn
  have hsign : (-1 : 𝕜)^(u.natDegree+n) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  symm
  rw [coeff_det_rationalModificationFirstRowMatrix_self T hu hn,
    det_rationalModificationFirstRowMatrix_eq, det_rationalModificationBorderMatrix_eq T hu hn,
    show (-1 : 𝕜[X])^(u.natDegree+n) = C ((-1 : 𝕜)^(u.natDegree+n)) by simp]
  simp only [smul_eq_C_mul]
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
  have hscalar : (u.leadingCoeff /
      ((-1 : 𝕜)^(u.natDegree+n) * (rationalModificationConstraintMatrix T u n).det)) *
      (-1 : 𝕜)^(u.natDegree+n) *
      ((rationalModificationConstraintMatrix T u n).det / u.leadingCoeff) = 1 := by
    field_simp
  rw [hscalar, C_1, one_mul]

/-- The source's actual first-row determinant, divided by its proved nonzero
normalization and the original numerator polynomial, is the canonical modified
monic orthogonal polynomial. The division is polynomial, including zeros of `u`.
Source: focused rational-modification reroute, determinant formula (CU4)--(CU5).
atlas: christoffel-uvarov-modification (partial) -/
theorem monicOrthogonalPolynomial_eq_rationalModification_det_div
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n =
      ((u.leadingCoeff /
        (rationalModificationFirstRowMatrix T u n).det.coeff (u.natDegree+n)) •
          (rationalModificationFirstRowMatrix T u n).det) / u := by
  rw [← rationalModificationNumerator_eq_smul_det_firstRowMatrix T hu hn,
    rationalModificationNumerator_eq_mul_monicOrthogonalPolynomial T hu hn,
    mul_div_cancel_left₀ _ hu]

end NLAlib
