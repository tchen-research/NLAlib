import NLAlib.Matrix.Spectral.AdjugateRankOne
import Mathlib.LinearAlgebra.Eigenspace.Basic
/-!
# The converse to paired deflation and the eigenvalue adjugate

An isolated similarity coordinate gives a paired right column and inverse
row. At geometric multiplicity one the adjugate is their nonzero rank-one
outer product, even when the eigenvalue is defective.
Source: Horn–Johnson (2013), Theorems 1.4.7 and 1.4.12.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- An isolated row and column under an invertible similarity supply nonzero
right and left eigenvectors with pairing one. Source: Horn–Johnson (2013),
Theorem 1.4.7, converse; the left vector is the corresponding inverse row.
atlas: left-right-eigenvectors -/
theorem eigenpair_of_isolated_similarity
    (A S : Matrix n n K) (i : n) (μ : K) (hS : IsUnit S)
    (hcol : ∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0)
    (hrow : ∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) :
    Matrix.col S i ≠ 0 ∧ (fun j => S⁻¹ i j) ≠ 0 ∧
    (fun j => S⁻¹ i j) ⬝ᵥ Matrix.col S i = 1 ∧
    A *ᵥ Matrix.col S i = μ • Matrix.col S i ∧
    (fun j => S⁻¹ i j) ᵥ* A = μ • (fun j => S⁻¹ i j) := by
  let := hS.nonempty_invertible.some
  have hpair : (fun j => S⁻¹ i j) ⬝ᵥ Matrix.col S i = 1 := by
    change (S⁻¹ * S) i i = 1
    rw [Matrix.inv_mul_of_invertible]
    simp
  have hx : Matrix.col S i ≠ 0 := by intro h; simp [h] at hpair
  have hy : (fun j => S⁻¹ i j) ≠ 0 := by intro h; rw [h, zero_dotProduct] at hpair; exact zero_ne_one hpair
  refine ⟨hx, hy, hpair, ?_, ?_⟩
  · have hAS : A * S = S * (S⁻¹ * A * S) := by
      simp only [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
    funext j
    change (A * S) j i = μ * S j i
    rw [hAS, Matrix.mul_apply]
    simp only [hcol, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact mul_comm _ _
  · have hSA : S⁻¹ * A = (S⁻¹ * A * S) * S⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]
    funext j
    change (S⁻¹ * A) i j = μ * S⁻¹ i j
    rw [hSA, Matrix.mul_apply]
    simp only [hrow, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- At geometric multiplicity one, the eigenvalue adjugate is a nonzero
scalar multiple of any nonzero right-column/left-row eigenvector pair.
Source: Horn–Johnson (2013), Theorem 1.4.12. Algebraic simplicity and nonzero
left–right pairing are not required, so defective eigenvalues are included.
atlas: left-right-eigenvectors -/
theorem exists_adjugate_shift_eq_smul_vecMulVec_of_finrank_eigenspace_eq_one
    {A : Matrix n n K} {x y : n → K} {μ : K}
    (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hdim : finrank K (Module.End.eigenspace A.toLin' μ) = 1) :
    ∃ γ : K, γ ≠ 0 ∧ (μ • (1 : Matrix n n K) - A).adjugate = γ • Matrix.vecMulVec x y := by
  have hker : LinearMap.ker (μ • (1 : Matrix n n K) - A).mulVecLin =
      Module.End.eigenspace A.toLin' μ := by
    ext z
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Module.End.mem_eigenspace_iff,
      Matrix.toLin'_apply, sub_eq_zero, eq_comm]
  apply exists_adjugate_eq_smul_vecMulVec_of_finrank_ker_eq_one _ hx hy
  · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAx, sub_self]
  · rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, hyA, sub_self]
  · rw [hker, hdim]

end NLAlib
