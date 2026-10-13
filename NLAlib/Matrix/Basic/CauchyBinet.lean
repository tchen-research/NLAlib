import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Real.Basic
import NLAlib.ForMathlib.Data.ExactRowSubset

/-!
# Cauchy–Binet and compound matrices

The polynomial identity `det(I+tXY)=det(I+tYX)` and the principal-minor
coefficient theorem give Cauchy–Binet without assumptions on the minors.
The same finite basis is used in both middle minors, so arbitrary finite
coordinate labels are supported. Horn–Johnson 2013, §§0.8.1 and 0.8.7.
-/

noncomputable section
open scoped Matrix
open Polynomial
namespace NLAlib
variable {r k R : Type*} [Fintype r] [Fintype k] [DecidableEq r] [DecidableEq k]
  [CommRing R]

/-- The subsets of a finite index type having the size of the given minor
coordinate type: `ExactRowSubset k (Fintype.card r)`. Horn–Johnson §0.8.7, compound matrix
index vocabulary. -/
abbrev SizedSubset (k r : Type*) [Fintype r] := ExactRowSubset k (Fintype.card r)

/-- A fixed coordinate listing of a sized subset, reused in both middle
minors of Cauchy–Binet. Its order may be arbitrary because the determinant
sign occurs in both factors and cancels. Horn–Johnson §0.8.1. -/
def sizedSubsetIndex (S : SizedSubset k r) : r → k :=
  fun i => ((Fintype.equivOfCardEq ((Fintype.card_coe S.val).trans S.property) : S.val ≃ r).symm i).val

private theorem coeff_card_det_one_add_X_smul (M : Matrix r r R) :
    (Matrix.det (1 + (X : R[X]) • M.map C)).coeff (Fintype.card r) = M.det := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  simp only [← Finset.card_univ (α := r), Finset.powersetCard_self, Finset.sum_singleton]
  let e : (Finset.univ : Finset r) ≃ r := Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)
  exact Matrix.det_submatrix_equiv_self e M

/-- Cauchy–Binet for a square product of rectangular matrices, over every
commutative ring and arbitrary finite labels. All middle minors, including
empty and rank-deficient ones, are included. Horn–Johnson 2013, §0.8.1.
atlas: cauchy-binet (partial) -/
theorem det_mul_eq_sum_det_submatrix_mul_det_submatrix (A : Matrix r k R) (B : Matrix k r R) :
    (A * B).det = ∑ S : SizedSubset k r,
      (A.submatrix id (sizedSubsetIndex S)).det *
        (B.submatrix (sizedSubsetIndex S) id).det := by
  have hPoly := Matrix.det_one_add_mul_comm ((X : R[X]) • A.map C) (B.map C)
  have hCoeff := congrArg (fun p : R[X] => p.coeff (Fintype.card r)) hPoly
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul] at hCoeff
  rw [coeff_card_det_one_add_X_smul,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors] at hCoeff
  rw [hCoeff]
  rw [← Finset.sum_attach]
  let e : {S // S ∈ (Finset.univ : Finset k).powersetCard (Fintype.card r)} ≃
      SizedSubset k r := Equiv.subtypeEquivRight fun S => by simp
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro S _
  let T := e S
  let eT : T.val ≃ r := Fintype.equivOfCardEq ((Fintype.card_coe T.val).trans T.property)
  have hSub : (B * A).submatrix (Subtype.val : T.val → k) (Subtype.val : T.val → k) =
      B.submatrix (Subtype.val : T.val → k) id * A.submatrix id (Subtype.val : T.val → k) := by
    simpa only [Equiv.coe_refl] using (Matrix.submatrix_mul_equiv B A
      (Subtype.val : T.val → k) (Equiv.refl r) (Subtype.val : T.val → k)).symm
  change ((B * A).submatrix (Subtype.val : T.val → k) (Subtype.val : T.val → k)).det = _
  rw [hSub, ← Matrix.det_reindex_self eT]
  rw [Matrix.reindex_apply, ← Matrix.submatrix_mul_equiv _ _ eT.symm (Equiv.refl r) eT.symm]
  simp only [Equiv.coe_refl, Matrix.submatrix_submatrix, Function.comp_id]
  rw [Matrix.det_mul]
  exact mul_comm _ _

variable {m n : Type*}

/-- A compound matrix consists of all minors of a fixed size. Each finite
subset receives a fixed coordinate order; every product uses that same order
on its shared middle subsets. Horn–Johnson 2013, §0.8.7.
atlas: cauchy-binet -/
def compoundMatrix (r : Type*) [Fintype r] [DecidableEq r] (A : Matrix m n R) :
    Matrix (SizedSubset m r) (SizedSubset n r) R := fun S T =>
  (A.submatrix (sizedSubsetIndex S) (sizedSubsetIndex T)).det

/-- Cauchy–Binet for every selected minor of a rectangular product. Repeated
outer labels are also allowed, and yield the usual zero determinant.
Horn–Johnson 2013, §0.8.1.
atlas: cauchy-binet (partial) -/
theorem det_submatrix_mul_eq_sum_minors (A : Matrix m k R) (B : Matrix k n R)
    (α : r → m) (β : r → n) :
    ((A * B).submatrix α β).det = ∑ S : SizedSubset k r,
      (A.submatrix α (sizedSubsetIndex S)).det *
        (B.submatrix (sizedSubsetIndex S) β).det := by
  have h := det_mul_eq_sum_det_submatrix_mul_det_submatrix
    (A.submatrix α id) (B.submatrix id β)
  have hProd : A.submatrix α id * B.submatrix id β = (A * B).submatrix α β :=
    Matrix.submatrix_mul_equiv A B α (Equiv.refl k) β
  simpa only [hProd, Matrix.submatrix_submatrix,
    Function.comp_id, Function.id_comp] using h

/-- Compounds are multiplicative in every size, with the shared subset
orientation occurring twice and hence cancelling. Horn–Johnson 2013, §0.8.7.
atlas: cauchy-binet (partial) -/
theorem compoundMatrix_mul (A : Matrix m k R) (B : Matrix k n R) :
    compoundMatrix r (A * B) = compoundMatrix r A * compoundMatrix r B := by
  ext S T
  exact det_submatrix_mul_eq_sum_minors A B (sizedSubsetIndex S) (sizedSubsetIndex T)

/-- A real column-Gram determinant is the sum of squares of all full-column
minors, including the empty determinant and matrices with too few rows.
Horn–Johnson 2013, §0.8.1.
atlas: cauchy-binet (partial) -/
theorem det_transpose_mul_self_eq_sum_det_sq [Fintype m] [DecidableEq m] (A : Matrix m r ℝ) :
    (Aᵀ * A).det = ∑ S : SizedSubset m r,
      (A.submatrix (sizedSubsetIndex S) id).det ^ 2 := by
  rw [det_mul_eq_sum_det_submatrix_mul_det_submatrix]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose, pow_two]

/-- Every clause of Cauchy–Binet: arbitrary product minors, compound
multiplicativity, and the real Gram sum of squared full-column minors.
All coordinate types are finite; no nonempty, rank or distinctness premise is
required. Horn–Johnson 2013, §§0.8.1 and 0.8.7.
atlas: cauchy-binet -/
theorem cauchy_binet_properties [Fintype m] [DecidableEq m] :
    (∀ (A : Matrix m k R) (B : Matrix k n R) (α : r → m) (β : r → n),
      ((A * B).submatrix α β).det = ∑ S : SizedSubset k r,
        (A.submatrix α (sizedSubsetIndex S)).det *
          (B.submatrix (sizedSubsetIndex S) β).det) ∧
    (∀ (A : Matrix m k R) (B : Matrix k n R),
      compoundMatrix r (A * B) = compoundMatrix r A * compoundMatrix r B) ∧
    (∀ A : Matrix m r ℝ, (Aᵀ * A).det = ∑ S : SizedSubset m r,
      (A.submatrix (sizedSubsetIndex S) id).det ^ 2) :=
  ⟨det_submatrix_mul_eq_sum_minors, compoundMatrix_mul,
    det_transpose_mul_self_eq_sum_det_sq⟩

end NLAlib
