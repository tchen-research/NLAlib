import NLAlib.Polynomial.OrthogonalPolynomials.ChristoffelFiniteCoefficients
import NLAlib.Matrix.Structured.BidiagonalDarboux

/-!
# Finite monic Jacobi factorization for a Christoffel modification

The native recurrence coefficients give the actual finite bidiagonal Darboux
factors. Reversing them gives the modified Jacobi matrix with its necessary
terminal-coordinate correction. Source: Gautschi (2004), Theorem 1.33;
operator derivations OP24.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜]

private theorem orthogonalRecurrenceBeta_eq_christoffelQuotient_mul_elimination
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {z : 𝕜}
    {n : ℕ} (hn : 0 < n)
    (hz : ∀ k ≤ n, (monicOrthogonalPolynomial L k).eval z ≠ 0) :
    orthogonalRecurrenceBeta L n =
      christoffelQuotient L z (n-1) * christoffelElimination L z (n-1) := by
  rw [christoffelElimination, show n-1+1 = n by omega]
  have hq : christoffelQuotient L z (n-1) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (by simpa only [show n-1+1=n by omega] using hz n le_rfl))
      (hz (n-1) (by omega))
  field_simp [hq]

private theorem monicJacobiMatrix_add_scalar_one (n : ℕ) (a b : ℕ → 𝕜) (z : 𝕜) :
    monicJacobiMatrix n (fun j => z + a j) b = monicJacobiMatrix n a b + z • 1 := by
  ext i j
  simp only [monicJacobiMatrix, Matrix.add_apply, diagonal_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  all_goals simp [hij]
  all_goals ring

private theorem monicJacobiMatrix_eq_of_coefficients {n : ℕ} {a a' b b' : ℕ → 𝕜}
    (ha : ∀ i < n, a i = a' i) (hb : ∀ i < n, 0 < i → b i = b' i) :
    monicJacobiMatrix n a b = monicJacobiMatrix n a' b' := by
  ext i j
  simp only [monicJacobiMatrix, Matrix.add_apply, diagonal_apply, Matrix.of_apply]
  rw [ha i.val i.isLt]
  by_cases hsub : j.val+1 = i.val
  · rw [if_pos hsub, if_pos hsub, hb i.val i.isLt (by omega)]
  · rw [if_neg hsub, if_neg hsub]

/-- The finite original monic Jacobi matrix minus the modification point is
exactly its lower/upper bidiagonal Darboux product, from finite-prefix hypotheses
through its dimension. Finite-support terminal matrices are included.
Source: Gautschi (2004), Theorem 1.33; operator derivations OP24.
atlas: kernel-polynomials-christoffel (partial) -/
theorem monicJacobiMatrix_sub_scalar_one_eq_christoffel_factors_of_finite
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {z : 𝕜} (n : ℕ)
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hz : ∀ k ≤ n, (monicOrthogonalPolynomial L k).eval z ≠ 0) :
    monicJacobiMatrix n (orthogonalRecurrenceAlpha L) (orthogonalRecurrenceBeta L) - z • 1 =
      darbouxLowerMatrix n (christoffelElimination L z) *
        darbouxUpperMatrix n (christoffelQuotient L z) := by
  have hJ : monicJacobiMatrix n (orthogonalRecurrenceAlpha L) (orthogonalRecurrenceBeta L) =
      monicJacobiMatrix n
        (fun j => z + (christoffelQuotient L z j +
          if j=0 then 0 else christoffelElimination L z (j-1)))
        (fun j => christoffelQuotient L z (j-1) * christoffelElimination L z (j-1)) := by
    apply monicJacobiMatrix_eq_of_coefficients
    · intro i hi
      rw [orthogonalRecurrenceAlpha_eq_add_christoffelQuotient_christoffelElimination_of_finite
        (fun k hk => hL k (by omega)) (fun k hk => hz k (by omega))]
      ring
    · intro i hin hi
      exact orthogonalRecurrenceBeta_eq_christoffelQuotient_mul_elimination hi
        (fun k hk => hz k (by omega))
  rw [hJ, monicJacobiMatrix_add_scalar_one, add_sub_cancel_right,
    darbouxLowerMatrix_mul_darbouxUpperMatrix]

/-- Reversing the actual finite Christoffel factors gives the modified monic
Jacobi matrix with its exact last-coordinate correction, using only finite
nondegeneracy through the dimension. Empty and terminal atomic dimensions are
included. Source: Gautschi (2004), Theorem 1.33; operator derivations OP24.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem monicJacobiMatrix_christoffel_eq_reversed_factors_add_boundary_of_finite
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {z : 𝕜} (n : ℕ)
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hz : ∀ k ≤ n, (monicOrthogonalPolynomial L k).eval z ≠ 0) :
    monicJacobiMatrix n
        (orthogonalRecurrenceAlpha (polynomialWeightedFunctional L (X-C z)))
        (orthogonalRecurrenceBeta (polynomialWeightedFunctional L (X-C z))) =
      darbouxUpperMatrix n (christoffelQuotient L z) *
        darbouxLowerMatrix n (christoffelElimination L z) + z • 1 +
          christoffelElimination L z (n-1) • terminalCoordinateMatrix n := by
  have hJ : monicJacobiMatrix n
        (orthogonalRecurrenceAlpha (polynomialWeightedFunctional L (X-C z)))
        (orthogonalRecurrenceBeta (polynomialWeightedFunctional L (X-C z))) =
      monicJacobiMatrix n
        (fun j => z + (christoffelQuotient L z j + christoffelElimination L z j))
        (fun j => christoffelQuotient L z j * christoffelElimination L z (j-1)) := by
    apply monicJacobiMatrix_eq_of_coefficients
    · intro i hi
      rw [orthogonalRecurrenceAlpha_polynomialWeightedFunctional_X_sub_C_of_finite
        (fun k hk => hL k (by omega)) (hz i (by omega)) (hz (i+1) (by omega))]
      ring
    · intro i hin hi
      exact orthogonalRecurrenceBeta_polynomialWeightedFunctional_X_sub_C_of_finite hi
        (fun k hk => hL k (by omega)) (fun k hk => hz k (by omega))
  rw [hJ, monicJacobiMatrix_add_scalar_one,
    monicJacobiMatrix_eq_darbouxUpperMatrix_mul_darbouxLowerMatrix_add_boundary]
  abel

/-- The globally quasi-definite original recurrence has the finite Darboux
factorization at every truncation size.
Source: Gautschi (2004), Theorem 1.33; AQ15.
atlas: kernel-polynomials-christoffel (partial) -/
theorem monicJacobiMatrix_sub_scalar_one_eq_christoffel_factors
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (hL : QuasiDefinitePolynomialFunctional L) {z : 𝕜}
    (hz : ∀ n, (monicOrthogonalPolynomial L n).eval z ≠ 0) (n : ℕ) :
    monicJacobiMatrix n (orthogonalRecurrenceAlpha L) (orthogonalRecurrenceBeta L) - z • 1 =
      darbouxLowerMatrix n (christoffelElimination L z) *
        darbouxUpperMatrix n (christoffelQuotient L z) :=
  monicJacobiMatrix_sub_scalar_one_eq_christoffel_factors_of_finite n
    (fun k _ => hL k) (fun k _ => hz k)

/-- The globally quasi-definite modified recurrence has the finite reversed
Darboux factorization with its exact terminal-coordinate correction.
Source: Gautschi (2004), Theorem 1.33; AQ15.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem monicJacobiMatrix_christoffel_eq_reversed_factors_add_boundary
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (hL : QuasiDefinitePolynomialFunctional L) {z : 𝕜}
    (hz : ∀ n, (monicOrthogonalPolynomial L n).eval z ≠ 0) (n : ℕ) :
    monicJacobiMatrix n
        (orthogonalRecurrenceAlpha (polynomialWeightedFunctional L (X-C z)))
        (orthogonalRecurrenceBeta (polynomialWeightedFunctional L (X-C z))) =
      darbouxUpperMatrix n (christoffelQuotient L z) *
        darbouxLowerMatrix n (christoffelElimination L z) + z • 1 +
          christoffelElimination L z (n-1) • terminalCoordinateMatrix n :=
  monicJacobiMatrix_christoffel_eq_reversed_factors_add_boundary_of_finite n
    (fun k _ => hL k) (fun k _ => hz k)

end NLAlib
