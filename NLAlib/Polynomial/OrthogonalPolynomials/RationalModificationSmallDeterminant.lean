import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationSmallSystem
import Mathlib.GroupTheory.Perm.Fin

/-! # Exact first-row normalization of the compressed CU determinant

Moving the polynomial row to the first position gives precisely the source
sign. The normalization coefficient is the proved nonzero actual constraint
minor, and polynomial division gives the canonical modified monic polynomial.
Source: focused mathematical reroutes, CU6--CU8.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜]

/-- The source compressed first-row determinant with the exact column range
`π_(max(n-m,0)),...,π_(n+degree u)` and the corrected number of inverse-moment
rows `min(n,m)`. -/
def rationalModificationSmallFirstRowMatrix (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (u v : 𝕜[X]) (n : ℕ) :
    Matrix (Fin (u.natDegree+min n v.natDegree+1))
      (Fin (u.natDegree+min n v.natDegree+1)) 𝕜[X] :=
  fun i j => if hi : i.val = 0 then monicOrthogonalPolynomial L (n-v.natDegree+j.val)
    else C (rationalModificationConstraint T u (min n v.natDegree)
      ⟨i.val-1, by have := i.isLt; omega⟩
        (monicOrthogonalPolynomial L (n-v.natDegree+j.val)))

private theorem base_add_small_size (u v : 𝕜[X]) (n : ℕ) :
    n-v.natDegree+(u.natDegree+min n v.natDegree) = u.natDegree+n := by omega

/-- Moving the actual small determinant's polynomial row from last to first
introduces exactly `(-1)^(degree u+min(n,m))`. -/
theorem det_rationalModificationSmallFirstRowMatrix_eq
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (u v : 𝕜[X]) (n : ℕ) :
    (rationalModificationSmallFirstRowMatrix L T u v n).det =
      (-1 : 𝕜[X])^(u.natDegree+min n v.natDegree) *
        (rationalModificationSmallBorderMatrix L T u v n).det := by
  let k := u.natDegree+min n v.natDegree
  let B := (rationalModificationSmallBorderMatrix L T u v n).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  have hlast (j : Fin (k+1)) :
      rationalModificationSmallBorderMatrix L T u v n (Sum.inr 0) (finSumFinEquiv.symm j) =
        monicOrthogonalPolynomial L (n-v.natDegree+j.val) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [finSumFinEquiv_symm_last, rationalModificationSmallBorderMatrix,
        fromBlocks_apply₂₂, Fin.val_last, k, base_add_small_size]
    · simp [rationalModificationSmallBorderMatrix]
  have hrow (i : Fin k) (j : Fin (k+1)) :
      rationalModificationSmallBorderMatrix L T u v n (Sum.inl i) (finSumFinEquiv.symm j) =
        C (rationalModificationConstraint T u (min n v.natDegree) i
          (monicOrthogonalPolynomial L (n-v.natDegree+j.val))) := by
    refine Fin.lastCases ?_ (fun t => ?_) j
    · simp only [finSumFinEquiv_symm_last, rationalModificationSmallBorderMatrix,
        fromBlocks_apply₁₂, rationalModificationSmallLeadingConstraints, Fin.val_last, k,
        base_add_small_size]
    · simp [rationalModificationSmallBorderMatrix, rationalModificationSmallMatrix]
  have hrows : rationalModificationSmallFirstRowMatrix L T u v n =
      B.submatrix (Fin.last k).cycleRange.symm id := by
    funext i j
    refine Fin.cases ?_ (fun t => ?_) i
    · simp only [rationalModificationSmallFirstRowMatrix, Fin.val_zero,
        Matrix.submatrix_apply, id_eq, B, Fin.cycleRange_symm_zero, k, finSumFinEquiv_symm_last]
      exact (hlast j).symm
    · simp only [rationalModificationSmallFirstRowMatrix, Fin.val_succ,
        dif_neg (show t.val+1 ≠ 0 by omega), Nat.add_sub_cancel,
        Matrix.submatrix_apply, id_eq, B, Fin.cycleRange_symm_succ,
        Fin.succAbove_last, finSumFinEquiv_symm_apply_castSucc]
      exact (hrow t j).symm
  rw [hrows, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
  simp [sign_finRotate, k]

/-- The top coefficient of the actual compressed last-row determinant is
exactly its native normalization minor. -/
theorem coeff_det_rationalModificationSmallBorderMatrix_self
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {u v : 𝕜[X]} (hu : u ≠ 0) (hv : v ≠ 0)
    (hTv : ∀ p, T (v*p) = L p) {n : ℕ}
    (hL : ∀ j ≤ u.natDegree+n, hankelMomentDet L j ≠ 0)
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    (rationalModificationSmallBorderMatrix L T u v n).det.coeff (u.natDegree+n) =
      (rationalModificationSmallMatrix L T u v n).det := by
  let π := monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n
  have hπ : π.Monic := monic_monicOrthogonalPolynomial _ _
  have hnat : (u*π).natDegree = u.natDegree+n := by
    rw [natDegree_mul hu hπ.ne_zero, natDegree_monicOrthogonalPolynomial]
  rw [det_rationalModificationSmallBorderMatrix_eq L T hu hv hTv hL hn, mul_assoc, coeff_C_mul]
  change _ * (u*π).coeff (u.natDegree+n) = _
  rw [← hnat, coeff_natDegree, leadingCoeff_mul, hπ.leadingCoeff, mul_one,
    div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hu)]

/-- The actual source normalization is `(-1)^k det M`, where
`k=degree u+min(n,degree v)`, and therefore is nonzero. Source: CU8.
atlas: christoffel-uvarov-modification (partial) -/
theorem coeff_det_rationalModificationSmallFirstRowMatrix_self_ne_zero
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {u v : 𝕜[X]} (hu : u ≠ 0) (hv : v ≠ 0)
    (hTv : ∀ p, T (v*p) = L p) {n : ℕ}
    (hL : ∀ j ≤ u.natDegree+n, hankelMomentDet L j ≠ 0)
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    (rationalModificationSmallFirstRowMatrix L T u v n).det.coeff (u.natDegree+n) ≠ 0 := by
  rw [det_rationalModificationSmallFirstRowMatrix_eq,
    show (-1 : 𝕜[X])^(u.natDegree+min n v.natDegree) =
      C ((-1 : 𝕜)^(u.natDegree+min n v.natDegree)) by simp,
    coeff_C_mul, coeff_det_rationalModificationSmallBorderMatrix_self L T hu hv hTv hL hn]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (det_rationalModificationSmallMatrix_ne_zero L T hu hv hTv (fun j hj => hL j hj.le) hn)

/-- The actual compressed first-row determinant divided by its proved nonzero
normalization and by `u` is the canonical modified monic polynomial. All
denominator degrees are allowed, and division by `u` is exact polynomial
division even at its roots. Source: focused mathematical reroutes CU6--CU8.
atlas: christoffel-uvarov-modification (partial) -/
theorem monicOrthogonalPolynomial_eq_rationalModification_small_det_div
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {u v : 𝕜[X]} (hu : u ≠ 0) (hv : v ≠ 0)
    (hTv : ∀ p, T (v*p) = L p) {n : ℕ}
    (hL : ∀ j ≤ u.natDegree+n, hankelMomentDet L j ≠ 0)
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n =
      ((u.leadingCoeff/
        (rationalModificationSmallFirstRowMatrix L T u v n).det.coeff (u.natDegree+n)) •
          (rationalModificationSmallFirstRowMatrix L T u v n).det) / u := by
  have hM := det_rationalModificationSmallMatrix_ne_zero L T hu hv hTv (fun j hj => hL j hj.le) hn
  have hlc := leadingCoeff_ne_zero.mpr hu
  have hs : (-1 : 𝕜)^(u.natDegree+min n v.natDegree) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [det_rationalModificationSmallFirstRowMatrix_eq,
    show (-1 : 𝕜[X])^(u.natDegree+min n v.natDegree) =
      C ((-1 : 𝕜)^(u.natDegree+min n v.natDegree)) by simp,
    coeff_C_mul, coeff_det_rationalModificationSmallBorderMatrix_self L T hu hv hTv hL hn,
    det_rationalModificationSmallBorderMatrix_eq L T hu hv hTv hL hn, smul_eq_C_mul]
  have hscalar : (u.leadingCoeff/((-1 : 𝕜)^(u.natDegree+min n v.natDegree) *
      (rationalModificationSmallMatrix L T u v n).det)) *
      (-1 : 𝕜)^(u.natDegree+min n v.natDegree) *
      ((rationalModificationSmallMatrix L T u v n).det/u.leadingCoeff) = 1 := by field_simp
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, hscalar, C_1, one_mul,
    mul_div_cancel_left₀ _ hu]

end NLAlib
