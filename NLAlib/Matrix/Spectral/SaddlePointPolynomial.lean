import NLAlib.Matrix.Structured.SaddlePoint
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Characteristic polynomial of a normalized saddle-point matrix

A Schur-complement determinant identity away from the scalar `1`, followed by
polynomial identity, proves the complete characteristic polynomial. This retains
all eigenvalue multiplicities without choosing singular vectors.
Source: the block spectral reduction of Benzi--Golub--Liesen (2005), §10.1.1.
-/

noncomputable section
open scoped Matrix Polynomial
open Polynomial
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

private theorem scalar_eq_smul_one {τ : Type*} [Fintype τ] [DecidableEq τ]
    (t : 𝕜) : Matrix.scalar τ t = t • (1 : Matrix τ τ 𝕜) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h]

/-- Schur-complement determinant formula at each scalar other than `1`. -/
theorem eval_charpoly_kktMatrix_one (C : Matrix m n 𝕜)
    (hmn : Fintype.card m ≤ Fintype.card n) {t : 𝕜} (ht : t ≠ 1) :
    (kktMatrix 1 C).charpoly.eval t =
      (t - 1) ^ (Fintype.card n - Fintype.card m) *
        (C * Cᴴ).charpoly.eval (t ^ 2 - t) := by
  have ht0 : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  let : Invertible ((t - 1) • (1 : Matrix n n 𝕜)) :=
    { invOf := (t - 1)⁻¹ • 1
      invOf_mul_self := by simp [smul_smul, ht0]
      mul_invOf_self := by simp [smul_smul, ht0] }
  have hblock : Matrix.scalar (n ⊕ m) t - kktMatrix 1 C =
      Matrix.fromBlocks ((t - 1) • 1) (-Cᴴ) (-C) (t • 1) := by
    rw [scalar_eq_smul_one, kktMatrix]
    ext (i | i) (j | j) <;>
      simp [Matrix.fromBlocks, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
    split_ifs <;> ring
  have hc : t * (t - 1) = t ^ 2 - t := by ring
  have hinner : t • (1 : Matrix m m 𝕜) -
      (-C) * ((t - 1)⁻¹ • (1 : Matrix n n 𝕜)) * (-Cᴴ) =
      (t - 1)⁻¹ • ((t ^ 2 - t) • (1 : Matrix m m 𝕜) - C * Cᴴ) := by
    have hcoeff : (t - 1)⁻¹ * (t ^ 2 - t) = t := by rw [← hc]; field_simp
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.neg_mul, Matrix.mul_neg, smul_neg, neg_neg, smul_sub, smul_smul, hcoeff]
  rw [Matrix.eval_charpoly, hblock, Matrix.det_fromBlocks₁₁]
  change ((t - 1) • (1 : Matrix n n 𝕜)).det *
    (t • (1 : Matrix m m 𝕜) - (-C) * ((t - 1)⁻¹ • (1 : Matrix n n 𝕜)) * (-Cᴴ)).det = _
  rw [hinner, Matrix.det_smul, Matrix.det_smul, Matrix.det_one, mul_one,
    Matrix.eval_charpoly, scalar_eq_smul_one, ← mul_assoc]
  congr 1
  rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ ht0), ← pow_add,
    Nat.sub_add_cancel hmn]

/-- The exact characteristic polynomial, including the rectangular unit-eigenvalue
multiplicity and all multiplicities of the Gram eigenvalues. -/
theorem charpoly_kktMatrix_one (C : Matrix m n 𝕜)
    (hmn : Fintype.card m ≤ Fintype.card n) :
    (kktMatrix 1 C).charpoly =
      (X - 1) ^ (Fintype.card n - Fintype.card m) *
        (C * Cᴴ).charpoly.comp (X ^ 2 - X) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.finite_singleton (1 : 𝕜)).infinite_compl.mono
  intro t ht
  have ht1 : t ≠ 1 := ht
  simpa only [Set.mem_ofPred_eq, eval_mul, eval_pow, eval_sub, eval_X, eval_one, eval_comp] using
    eval_charpoly_kktMatrix_one C hmn ht1

/-- Every Gram eigenvalue contributes its quadratic factor, with multiplicity. -/
theorem charpoly_kktMatrix_one_eq_prod (C : Matrix m n 𝕜)
    (hmn : Fintype.card m ≤ Fintype.card n) :
    (kktMatrix 1 C).charpoly =
      (X - 1) ^ (Fintype.card n - Fintype.card m) *
        ∏ i, (X ^ 2 - X - Polynomial.C
          ((Matrix.isHermitian_mul_conjTranspose_self C).eigenvalues i : 𝕜)) := by
  rw [charpoly_kktMatrix_one C hmn, (Matrix.isHermitian_mul_conjTranspose_self C).charpoly_eq]
  simp only [prod_comp, sub_comp, X_comp, C_comp]

end NLAlib
