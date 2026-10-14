import NLAlib.Polynomial.OrthogonalPolynomials.Christoffel
import NLAlib.Polynomial.OrthogonalPolynomials.Kernel

/-! # Christoffel modification as a reproducing kernel

The linear-modification quotient equals the scaled monic reproducing kernel.
The argument is a polynomial identity, including its value at the modification
point; no nonzero transformed value at that point is assumed.
Source: Gautschi (2004), Theorem 1.33; operator derivation AQ12.
-/

noncomputable section

open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- The Christoffel quotient is the monic reproducing kernel scaled by
`h_n / π_n(z)`. Source: Gautschi (2004), Theorem 1.33.
atlas: kernel-polynomials-christoffel (partial) -/
theorem christoffelPolynomial_eq_C_mul_monicOrthogonalKernelPolynomial
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0)
    {z : 𝕜} (hz : (monicOrthogonalPolynomial L n).eval z ≠ 0) :
    christoffelPolynomial L z n =
      C (orthogonalPolynomialNorm L n / (monicOrthogonalPolynomial L n).eval z) *
        monicOrthogonalKernelPolynomial L (n + 1) z := by
  have hnorm : orthogonalPolynomialNorm L n ≠ 0 :=
    (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL n (by omega))).functional_sq_ne_zero
      (hL (n + 1) le_rfl)
  have h := congrArg
    (fun p : 𝕜[X] => C (orthogonalPolynomialNorm L n /
      (monicOrthogonalPolynomial L n).eval z) * p)
    (X_sub_C_mul_monicOrthogonalKernelPolynomial n hL z)
  have hc1 : C (orthogonalPolynomialNorm L n / (monicOrthogonalPolynomial L n).eval z) *
      C ((monicOrthogonalPolynomial L n).eval z / orthogonalPolynomialNorm L n) =
        (1 : 𝕜[X]) := by
    rw [← map_mul, ← C_1]
    congr 1
    field_simp
  have hc2 : C (orthogonalPolynomialNorm L n / (monicOrthogonalPolynomial L n).eval z) *
      C ((monicOrthogonalPolynomial L (n + 1)).eval z / orthogonalPolynomialNorm L n) =
        C ((monicOrthogonalPolynomial L (n + 1)).eval z /
          (monicOrthogonalPolynomial L n).eval z) := by
    rw [← map_mul]
    congr 1
    field_simp
  simp only [mul_sub, ← mul_assoc, hc1, one_mul, hc2] at h
  apply mul_left_cancel₀ (monic_X_sub_C z).ne_zero
  rw [X_sub_C_mul_christoffelPolynomial L n hz]
  rw [← h]
  ring

end NLAlib
