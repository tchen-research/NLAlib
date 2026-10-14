import NLAlib.Polynomial.OrthogonalPolynomials.Recurrence

/-! # Normalized finite-moment polynomials

Positive squared norms normalize the canonical monic moment polynomials into
an orthonormal family. Normalization remains total, with value zero whenever
the square root of the squared norm vanishes.
Source: Gautschi (2004), Section 1.1.
-/

noncomputable section

open Polynomial Finset

namespace NLAlib

/-- The canonical monic moment polynomial divided by the positive square root
of its squared norm. Its total value is zero if that square root vanishes. -/
def orthonormalMomentPolynomial (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) : ℝ[X] :=
  C (Real.sqrt (orthogonalPolynomialNorm L n))⁻¹ * monicOrthogonalPolynomial L n

/-- Positive squared norm preserves the exact degree under normalization. -/
theorem degree_orthonormalMomentPolynomial {L : ℝ[X] →ₗ[ℝ] ℝ} {n : ℕ}
    (hH : 0 < orthogonalPolynomialNorm L n) :
    (orthonormalMomentPolynomial L n).degree = n := by
  rw [orthonormalMomentPolynomial, degree_C_mul (inv_ne_zero (Real.sqrt_pos.mpr hH).ne'),
    degree_eq_natDegree (monic_monicOrthogonalPolynomial L n).ne_zero,
    natDegree_monicOrthogonalPolynomial]

/-- Positive-norm monic moment polynomials are recovered from their normalized
versions by multiplication by the square-root norm. -/
theorem sqrt_norm_mul_orthonormalMomentPolynomial {L : ℝ[X] →ₗ[ℝ] ℝ} {n : ℕ}
    (hH : 0 < orthogonalPolynomialNorm L n) :
    C (Real.sqrt (orthogonalPolynomialNorm L n)) * orthonormalMomentPolynomial L n =
      monicOrthogonalPolynomial L n := by
  rw [orthonormalMomentPolynomial, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hH).ne', C_1, one_mul]

/-- Nonsingular moment systems and positive squared norms give normalized
bilinear orthonormality. -/
theorem functional_orthonormalMomentPolynomial_mul (L : ℝ[X] →ₗ[ℝ] ℝ) {i j : ℕ}
    (hi : hankelMomentDet L i ≠ 0) (hj : hankelMomentDet L j ≠ 0)
    (hHi : 0 < orthogonalPolynomialNorm L i) (hHj : 0 < orthogonalPolynomialNorm L j) :
    L (orthonormalMomentPolynomial L i * orthonormalMomentPolynomial L j) =
      if i = j then 1 else 0 := by
  rw [orthonormalMomentPolynomial, orthonormalMomentPolynomial]
  rw [show C (Real.sqrt (orthogonalPolynomialNorm L i))⁻¹ * monicOrthogonalPolynomial L i *
      (C (Real.sqrt (orthogonalPolynomialNorm L j))⁻¹ * monicOrthogonalPolynomial L j) =
      C ((Real.sqrt (orthogonalPolynomialNorm L i))⁻¹ *
        (Real.sqrt (orthogonalPolynomialNorm L j))⁻¹) *
        (monicOrthogonalPolynomial L i * monicOrthogonalPolynomial L j) by
      rw [C_mul]; ring, C_mul', map_smul, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    rw [← pow_two (monicOrthogonalPolynomial L i)]
    change (Real.sqrt (orthogonalPolynomialNorm L i))⁻¹ *
      (Real.sqrt (orthogonalPolynomialNorm L i))⁻¹ * orthogonalPolynomialNorm L i = 1
    rw [← mul_inv, ← pow_two, Real.sq_sqrt hHi.le, inv_mul_cancel₀ hHi.ne']
  · rw [functional_monicOrthogonalPolynomial_mul_eq_zero_of_ne L hi hj hij,
      if_neg hij, mul_zero]

end NLAlib
