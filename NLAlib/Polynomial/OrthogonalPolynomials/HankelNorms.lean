import NLAlib.Polynomial.OrthogonalPolynomials.Recurrence
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Hankel determinants as products of monic norms

The monic coefficient matrix is unit upper triangular. Congruence by this
matrix turns the Hankel moment matrix into the diagonal monic Gram matrix.
This works for bilinear quasi-definite functionals over any field.
Source: Gautschi (2004), Chapter 1; operator derivations OF5–OF6.
-/

noncomputable section

open Polynomial Matrix Finset
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- The square matrix of monic polynomial coefficients, with polynomial
orders as columns and monomial degrees as rows. -/
def monicOrthogonalCoefficientMatrix (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    Matrix (Fin n) (Fin n) 𝕜 := fun i j => (monicOrthogonalPolynomial L j.val).coeff i.val

/-- The monic coefficient change of basis has determinant one, regardless
of moment-system singularities. -/
theorem det_monicOrthogonalCoefficientMatrix (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    (monicOrthogonalCoefficientMatrix L n).det = 1 := by
  have htri : (monicOrthogonalCoefficientMatrix L n).IsUpperTriangular := by
    intro i j hij
    exact coeff_eq_zero_of_natDegree_lt
      (by change j.val < i.val at hij
          simpa only [natDegree_monicOrthogonalPolynomial] using hij)
  rw [det_of_isUpperTriangular htri]
  apply prod_eq_one
  intro i _
  simpa only [monicOrthogonalCoefficientMatrix, natDegree_monicOrthogonalPolynomial] using
    (monic_monicOrthogonalPolynomial L i.val).coeff_natDegree

private theorem functional_sum_monomial_mul_eq (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ)
    (c d : Fin n → 𝕜) :
    L ((∑ i : Fin n, monomial i.val (c i)) *
      (∑ j : Fin n, monomial j.val (d j))) =
      ∑ i : Fin n, ∑ j : Fin n, c i * L (X ^ (i.val + j.val)) * d j := by
  simp only [sum_mul, mul_sum, map_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [monomial_mul_monomial, ← C_mul_X_pow_eq_monomial, C_mul', map_smul]
  simp only [smul_eq_mul]
  ring

/-- Monic coefficient congruence diagonalizes the finite bilinear Hankel
matrix whenever the lower-degree orthogonality systems are nonsingular.
Source: Gautschi (2004), Chapter 1. -/
theorem transpose_coefficientMatrix_mul_hankel_mul_coefficientMatrix
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ)
    (hL : ∀ k < n, hankelMomentDet L k ≠ 0) :
    (monicOrthogonalCoefficientMatrix L n)ᵀ * hankelMomentMatrix L n *
      monicOrthogonalCoefficientMatrix L n =
        diagonal (fun i : Fin n => orthogonalPolynomialNorm L i.val) := by
  have hP (i : Fin n) : (monicOrthogonalPolynomial L i.val).degree < n := by
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L i.val).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast i.isLt
  ext i j
  rw [mul_apply]
  simp only [mul_apply, transpose_apply, monicOrthogonalCoefficientMatrix,
    hankelMomentMatrix]
  simp only [sum_mul]
  rw [sum_comm]
  have hform := functional_sum_monomial_mul_eq L n
    (fun k => (monicOrthogonalPolynomial L i.val).coeff k.val)
    (fun k => (monicOrthogonalPolynomial L j.val).coeff k.val)
  rw [← eq_sum_monomial_fin_of_degree_lt (hP i),
    ← eq_sum_monomial_fin_of_degree_lt (hP j)] at hform
  rw [← hform]
  by_cases hij : i = j
  · subst j
    simp only [diagonal_apply_eq, orthogonalPolynomialNorm, pow_two]
  · rw [diagonal_apply_ne _ hij]
    exact functional_monicOrthogonalPolynomial_mul_eq_zero_of_ne L
      (hL i.val i.isLt) (hL j.val j.isLt)
      (fun h => hij (Fin.ext h))

/-- A nonsingular finite orthogonality hierarchy has Hankel determinant
equal to the product of its monic squared bilinear norms.
Source: Gautschi (2004), Chapter 1, OF5.
atlas: hankel-moment-positivity (partial), monic-orthogonal-recurrence (partial) -/
theorem hankelMomentDet_eq_prod_orthogonalPolynomialNorm (L : 𝕜[X] →ₗ[𝕜] 𝕜)
    (n : ℕ) (hL : ∀ k < n, hankelMomentDet L k ≠ 0) :
    hankelMomentDet L n = ∏ i : Fin n, orthogonalPolynomialNorm L i.val := by
  have h := congrArg Matrix.det
    (transpose_coefficientMatrix_mul_hankel_mul_coefficientMatrix L n hL)
  simpa only [det_mul, det_transpose, det_monicOrthogonalCoefficientMatrix,
    one_mul, mul_one, det_diagonal, hankelMomentDet] using h

/-- Consecutive Hankel determinants recover each monic squared norm.
Source: Gautschi (2004), Chapter 1, OF5.
atlas: hankel-moment-positivity (partial), monic-orthogonal-recurrence (partial) -/
theorem orthogonalPolynomialNorm_eq_div_hankelMomentDet
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ)
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0) :
    orthogonalPolynomialNorm L n = hankelMomentDet L (n + 1) / hankelMomentDet L n := by
  have hnext := hankelMomentDet_eq_prod_orthogonalPolynomialNorm L (n + 1)
    (fun k hk => hL k (by omega))
  have hprev := hankelMomentDet_eq_prod_orthogonalPolynomialNorm L n (fun k hk => hL k (by omega))
  rw [Fin.prod_univ_castSucc] at hnext
  simp only [Fin.val_castSucc, Fin.val_last] at hnext
  rw [← hprev] at hnext
  rw [hnext, mul_div_cancel_left₀ _ (hL n (by omega))]

/-- The positive-order monic recurrence subdiagonal is the ratio of three
consecutive Hankel determinants. Source: Gautschi (2004), Chapter 1, OF6.
atlas: hankel-moment-positivity (partial), monic-orthogonal-recurrence (partial) -/
theorem orthogonalRecurrenceBeta_eq_hankelMomentDet_ratio
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {n : ℕ} (hn : 0 < n)
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0) :
    orthogonalRecurrenceBeta L n = hankelMomentDet L (n + 1) * hankelMomentDet L (n - 1) /
      hankelMomentDet L n ^ 2 := by
  rw [orthogonalRecurrenceBeta, if_neg hn.ne',
    orthogonalPolynomialNorm_eq_div_hankelMomentDet L n hL,
    orthogonalPolynomialNorm_eq_div_hankelMomentDet L (n - 1) (fun k hk => hL k (by omega)),
    show n - 1 + 1 = n by omega]
  field_simp [hL n (by omega), hL (n - 1) (by omega)]

end NLAlib
