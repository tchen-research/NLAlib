import NLAlib.Matrix.Spectral.EigenvectorPairing

/-!
# Rank-one eigenvalue shifts

Updating by an eigenvector outer product replaces one occurrence of its
eigenvalue in the characteristic polynomial. The quotient is a polynomial,
so the formula remains valid at the old eigenvalue and at repeated roots.
Source: Horn–Johnson (2013), Exercise 1.2.8 and Theorem 2.4.10.1;
atlas `rank-one-eigenvalue-update`.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The determinant lemma in outer-product notation. Source: Horn–Johnson
(2013), §0.8.5; this is Mathlib's matrix determinant lemma specialized to
one-column updates. -/
theorem det_add_vecMulVec {M : Matrix n n K} (hM : IsUnit M.det) (u v : n → K) :
    (M + Matrix.vecMulVec u v).det = M.det * (1 + v ⬝ᵥ (M⁻¹ *ᵥ u)) := by
  have hfactor : M + Matrix.vecMulVec u v =
      M * (1 + Matrix.vecMulVec (M⁻¹ *ᵥ u) v) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]
  rw [hfactor, Matrix.det_mul, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]

/-- A nonzero eigenvector forces its eigenvalue to be a characteristic root.
Source: Horn–Johnson (2013), Definition 1.4.6; includes no diagonalizability
assumption. -/
theorem isRoot_charpoly_of_mulVec_eq_smul {A : Matrix n n K} {x : n → K}
    {μ : K} (hx : x ≠ 0) (hAx : A *ᵥ x = μ • x) : A.charpoly.IsRoot μ := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  exact ⟨x, hx, by rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hAx, sub_self]⟩

/-- Away from the old spectrum, the characteristic-polynomial shift follows
from the determinant lemma and the inverse action on the eigenvector.
Source: Horn–Johnson (2013), Theorem 2.4.10.1. -/
theorem eval_charpoly_add_vecMulVec_mul_sub {A : Matrix n n K} {x : n → K}
    {μ : K} (hx : x ≠ 0) (hAx : A *ᵥ x = μ • x) (y : n → K) {z : K}
    (hz : A.charpoly.eval z ≠ 0) :
    (z - μ) * (A + Matrix.vecMulVec x y).charpoly.eval z =
      (z - μ - y ⬝ᵥ x) * A.charpoly.eval z := by
  let M : Matrix n n K := z • 1 - A
  have hMdet : M.det ≠ 0 := by
    simpa only [M, Matrix.eval_charpoly, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal] using hz
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hMdet
  have hzμ : z - μ ≠ 0 := by
    intro heq
    have hzEq : z = μ := sub_eq_zero.mp heq
    exact hz (hzEq ▸ (isRoot_charpoly_of_mulVec_eq_smul hx hAx).eq_zero)
  have hMx : M *ᵥ x = (z - μ) • x := by
    simp only [M, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAx,
      sub_smul]
  have hinv : M⁻¹ *ᵥ x = (z - μ)⁻¹ • x := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr ((M.isUnit_iff_isUnit_det).mpr hM)
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec,
      Matrix.mulVec_smul, hMx, smul_smul, inv_mul_cancel₀ hzμ, one_smul]
  have hshift : z • (1 : Matrix n n K) - (A + Matrix.vecMulVec x y) =
      M + Matrix.vecMulVec (-x) y := by
    simp only [M, Matrix.neg_vecMulVec]
    abel
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    hshift, det_add_vecMulVec hM]
  rw [Matrix.mulVec_neg, hinv, dotProduct_neg, dotProduct_smul]
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  simp only [smul_eq_mul, ← sub_eq_add_neg]
  change (z - μ) * (M.det * (1 - (z - μ)⁻¹ * (y ⬝ᵥ x))) =
    (z - μ - y ⬝ᵥ x) * M.det
  field_simp

/-- The rank-one eigenvalue update satisfies a polynomial cross-product
identity, including every value of the polynomial variable. Source:
Horn–Johnson (2013), Theorem 2.4.10.1; the infinite-field proof extends the
determinant-lemma computation across the finite old spectrum. -/
theorem charpoly_add_vecMulVec_mul_X_sub_C [Infinite K] {A : Matrix n n K}
    {x : n → K} {μ : K} (hx : x ≠ 0) (hAx : A *ᵥ x = μ • x) (y : n → K) :
    (X - C μ) * (A + Matrix.vecMulVec x y).charpoly =
      (X - C (μ + y ⬝ᵥ x)) * A.charpoly := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hfinite := Polynomial.finite_setOfPred_isRoot A.charpoly_monic.ne_zero
  apply hfinite.infinite_compl.mono
  intro z hz
  have hz' : A.charpoly.eval z ≠ 0 := hz
  simpa only [Set.mem_ofPred_eq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_add_eq_sub_sub] using
    eval_charpoly_add_vecMulVec_mul_sub hx hAx y hz'

/-- A rank-one update along a nonzero right eigenvector replaces exactly one
occurrence of the eigenvalue: the unchanged polynomial factor is shared by
the old and updated characteristic polynomials. Source: Horn–Johnson (2013),
Exercise 1.2.8 and Theorem 2.4.10.1. Over the complex field take `y = star v`
for the update `x v*`. Repeated eigenvalues and zero shifts are included;
the quotient is polynomial division, with no pointwise division at `μ`.
atlas: rank-one-eigenvalue-update -/
theorem exists_charpoly_factor_add_vecMulVec [Infinite K] {A : Matrix n n K}
    {x : n → K} {μ : K} (hx : x ≠ 0) (hAx : A *ᵥ x = μ • x) (y : n → K) :
    ∃ q : K[X], A.charpoly = (X - C μ) * q ∧
      (A + Matrix.vecMulVec x y).charpoly = (X - C (μ + y ⬝ᵥ x)) * q := by
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr (isRoot_charpoly_of_mulVec_eq_smul hx hAx)
  refine ⟨q, hq, ?_⟩
  apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero μ)
  rw [charpoly_add_vecMulVec_mul_X_sub_C hx hAx y, hq]
  ring

end NLAlib
