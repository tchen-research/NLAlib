import NLAlib.Matrix.Inequalities.AccretiveKernels
import NLAlib.Matrix.Factorizations.RowInclusionKernel

/-!
# Leading row and column inclusion for accretive matrices

Equality of the matrix rank and Hermitian-part rank identifies their kernels.
Positivity then promotes a null relation on a principal block to a global
null relation, giving both leading row and column inclusion.
Source: Horn–Johnson (2013), Lemma 7.1.11, Observation 7.1.12 and Corollary 7.1.13;
operator derivations, (S12). Atlas: `psd-hermitian-part`.
-/

noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- If an accretive matrix and its Hermitian part have equal rank, their
kernels coincide. Source: Horn–Johnson (2013), Observation 7.1.12.
atlas: psd-hermitian-part (partial) -/
theorem ker_mulVecLin_eq_selfAdjointPart_of_rank_eq {A : Matrix n n ℂ}
    (hA : (selfAdjointPart ℝ A : Matrix n n ℂ).PosSemidef)
    (hrank : (selfAdjointPart ℝ A : Matrix n n ℂ).rank = A.rank) :
    LinearMap.ker A.mulVecLin =
      LinearMap.ker (selfAdjointPart ℝ A : Matrix n n ℂ).mulVecLin := by
  have hker : LinearMap.ker A.mulVecLin ≤
      LinearMap.ker (selfAdjointPart ℝ A : Matrix n n ℂ).mulVecLin := by
    intro x hx
    exact selfAdjointPart_mulVec_eq_zero_of_mulVec_eq_zero hA hx
  apply Submodule.eq_of_le_of_finrank_eq hker
  have hdA := A.mulVecLin.finrank_range_add_finrank_ker
  have hdH := (selfAdjointPart ℝ A : Matrix n n ℂ).mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank at hrank
  omega

omit [Fintype n] [DecidableEq n] in
/-- Taking the Hermitian part commutes with forming a principal submatrix. -/
theorem selfAdjointPart_submatrix (A : Matrix n n ℂ) {m : Type*} (e : m → n) :
    (selfAdjointPart ℝ (A.submatrix e e) : Matrix m m ℂ) =
      (selfAdjointPart ℝ A : Matrix n n ℂ).submatrix e e := by
  ext i j
  simp [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose]

/-- A matrix with positive definite Hermitian part is invertible, including
the empty square matrix. Source: Horn–Johnson (2013), Corollary 7.1.13.
atlas: psd-hermitian-part (partial) -/
theorem isUnit_of_posDef_selfAdjointPart {A : Matrix n n ℂ}
    (hA : (selfAdjointPart ℝ A : Matrix n n ℂ).PosDef) : IsUnit A := by
  have hzero : ∀ x : n → ℂ, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hHx := selfAdjointPart_mulVec_eq_zero_of_mulVec_eq_zero hA.posSemidef hx
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hA.isUnit)
      (hHx.trans (Matrix.mulVec_zero _).symm)
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply sub_eq_zero.mp
  exact hzero (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])

omit [Fintype n] [DecidableEq n] in
/-- Every principal submatrix of a matrix with positive definite Hermitian
part is invertible. Index embeddings cover every principal cut.
Source: Horn–Johnson (2013), Corollary 7.1.13.
atlas: psd-hermitian-part (partial) -/
theorem isUnit_submatrix_of_posDef_selfAdjointPart {A : Matrix n n ℂ}
    (hA : (selfAdjointPart ℝ A : Matrix n n ℂ).PosDef)
    {m : Type*} [Fintype m] [DecidableEq m] (e : m → n) (he : Function.Injective e) :
    IsUnit (A.submatrix e e) := by
  apply isUnit_of_posDef_selfAdjointPart
  rw [selfAdjointPart_submatrix]
  exact hA.submatrix he

section Leading
variable [LinearOrder n]

omit [DecidableEq n] in
/-- An accretive matrix has leading row inclusion when its Hermitian part
has the same rank. This statement is complex and permits singular matrices.
Source: Horn–Johnson (2013), Observation 7.1.12; operator derivations, (S12).
atlas: psd-hermitian-part (partial) -/
theorem hasRowInclusion_of_posSemidef_selfAdjointPart_of_rank_eq
    {A : Matrix n n ℂ} (hA : (selfAdjointPart ℝ A : Matrix n n ℂ).PosSemidef)
    (hrank : (selfAdjointPart ℝ A : Matrix n n ℂ).rank = A.rank) :
    HasRowInclusion A := by
  apply hasRowInclusion_of_prefix_kernel
  intro i x hx hAx
  have hquad : quadForm A x = 0 := by
    unfold quadForm dotProduct
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j < i
    · simp [hAx j hj]
    · simp [hx j hj]
  have hH : (selfAdjointPart ℝ A : Matrix n n ℂ) *ᵥ x = 0 := by
    apply (hA.dotProduct_mulVec_zero_iff x).mp
    change quadForm (selfAdjointPart ℝ A : Matrix n n ℂ) x = 0
    rw [quadForm_selfAdjointPart, hquad]
    rfl
  have hzero : A *ᵥ x = 0 := by
    have hh : x ∈ LinearMap.ker (selfAdjointPart ℝ A : Matrix n n ℂ).mulVecLin := hH
    rw [← ker_mulVecLin_eq_selfAdjointPart_of_rank_eq hA hrank] at hh
    exact hh
  exact congrFun hzero i

omit [DecidableEq n] in
/-- An accretive matrix has leading column inclusion when its Hermitian
part has the same rank. Adjoint row inclusion supplies the conjugated
coefficients in the existing transpose-based column predicate.
Source: Horn–Johnson (2013), Observation 7.1.12; operator derivations, (S12).
atlas: psd-hermitian-part (partial) -/
theorem hasColumnInclusion_of_posSemidef_selfAdjointPart_of_rank_eq
    {A : Matrix n n ℂ} (hA : (selfAdjointPart ℝ A : Matrix n n ℂ).PosSemidef)
    (hrank : (selfAdjointPart ℝ A : Matrix n n ℂ).rank = A.rank) :
    HasColumnInclusion A := by
  have hpart : (selfAdjointPart ℝ Aᴴ : Matrix n n ℂ) = selfAdjointPart ℝ A := by
    simp [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose, add_comm]
  have hRow : HasRowInclusion Aᴴ :=
    hasRowInclusion_of_posSemidef_selfAdjointPart_of_rank_eq (hpart.symm ▸ hA)
      (by rw [hpart, Matrix.rank_conjTranspose]; exact hrank)
  intro i
  obtain ⟨c, hc, hcoeff⟩ := hRow i
  refine ⟨star c, fun j hj => by simp [hc j hj], ?_⟩
  intro k hk
  have h := congrArg star (hcoeff k hk)
  simpa [Matrix.conjTranspose_apply, map_sum, star_mul, mul_comm] using h

omit [DecidableEq n] in
/-- Positive definite Hermitian part ensures both row and column inclusion.
All principal blocks are invertible; no rank-equality premise is needed.
Source: Horn–Johnson (2013), Corollary 7.1.13; operator derivations, (S12).
atlas: psd-hermitian-part (partial) -/
theorem hasRowInclusion_and_hasColumnInclusion_of_posDef_selfAdjointPart
    {A : Matrix n n ℂ} (hA : (selfAdjointPart ℝ A : Matrix n n ℂ).PosDef) :
    HasRowInclusion A ∧ HasColumnInclusion A := by
  have hrank : (selfAdjointPart ℝ A : Matrix n n ℂ).rank = A.rank := by
    rw [Matrix.rank_of_isUnit _ hA.isUnit,
      Matrix.rank_of_isUnit _ (isUnit_of_posDef_selfAdjointPart hA)]
  exact ⟨hasRowInclusion_of_posSemidef_selfAdjointPart_of_rank_eq hA.posSemidef hrank,
    hasColumnInclusion_of_posSemidef_selfAdjointPart_of_rank_eq hA.posSemidef hrank⟩

end Leading
end NLAlib
