import NLAlib.Polynomial.OrthogonalPolynomials.NormSensitivity
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Moment sensitivity of monic subdiagonal coefficients

The quotient rule and orthogonality cancellation give the exact sensitivity
polynomial at every positive order. The order-zero recurrence boundary is zero;
the total-mass output has a separate derivative. Source: AQ27–AQ28 and AQ31 in
the operator re-derivations, Gautschi (2004), §2.1.
-/

noncomputable section
open Polynomial
namespace NLAlib

set_option backward.isDefEq.respectTransparency false

/-- The monic moment sensitivity polynomial for a positive-order norm quotient. -/
def orthogonalRecurrenceBetaSensitivityPolynomial (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) : ℝ[X] :=
  C (orthogonalRecurrenceBeta L n) *
    (C (orthogonalPolynomialNorm L n)⁻¹ * monicOrthogonalPolynomial L n ^ 2 -
      C (orthogonalPolynomialNorm L (n - 1))⁻¹ * monicOrthogonalPolynomial L (n - 1) ^ 2)

/-- The actual derivative of the monic subdiagonal norm quotient is evaluation
of the sensitivity polynomial by the moment variation. Source: AQ28.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem hasDerivAt_orthogonalRecurrenceBeta
    {L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)} {D : ℝ[X] →ₗ[ℝ] ℝ} {n : ℕ} {x : ℝ}
    (hn0 : 0 < n)
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hD : ∀ k, HasDerivAt (fun y => L y (X ^ k)) (D (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0)
    (hprev : hankelMomentDet (L x) (n - 1) ≠ 0)
    (hh : orthogonalPolynomialNorm (L x) n ≠ 0)
    (hhprev : orthogonalPolynomialNorm (L x) (n - 1) ≠ 0) :
    HasDerivAt (fun y => orthogonalRecurrenceBeta (L y) n)
      (D (orthogonalRecurrenceBetaSensitivityPolynomial (L x) n)) x := by
  have h := (hasDerivAt_orthogonalPolynomialNorm hL hD hn).fun_div
    (hasDerivAt_orthogonalPolynomialNorm hL hD hprev) hhprev
  have heq : D (orthogonalRecurrenceBetaSensitivityPolynomial (L x) n) =
      (D (monicOrthogonalPolynomial (L x) n ^ 2) * orthogonalPolynomialNorm (L x) (n - 1) -
        orthogonalPolynomialNorm (L x) n * D (monicOrthogonalPolynomial (L x) (n - 1) ^ 2)) /
          orthogonalPolynomialNorm (L x) (n - 1) ^ 2 := by
    simp only [orthogonalRecurrenceBetaSensitivityPolynomial, orthogonalRecurrenceBeta,
      if_neg hn0.ne', C_mul', map_smul, map_sub, smul_eq_mul]
    field_simp
  rw [heq]
  convert h using 1
  all_goals first | rfl | simp [orthogonalRecurrenceBeta, hn0.ne']

/-- The mass coordinate's moment derivative is `D(1)`, independently of the
zero order recurrence-boundary convention. Source: AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem hasDerivAt_mass_of_moment_derivatives
    {L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)} {D : ℝ[X] →ₗ[ℝ] ℝ} {x : ℝ}
    (hD : ∀ k, HasDerivAt (fun y => L y (X ^ k)) (D (X ^ k)) x) :
    HasDerivAt (fun y => L y 1) (D 1) x := by
  simpa using hD 0

/-- An arbitrary affine moment perturbation has the exact positive-order
subdiagonal directional derivative. Fixed-basis dual functionals specialize
this to the partial derivatives in AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem hasDerivAt_orthogonalRecurrenceBeta_affine
    (L D : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hn0 : 0 < n)
    (hn : hankelMomentDet L n ≠ 0)
    (hprev : hankelMomentDet L (n - 1) ≠ 0)
    (hh : orthogonalPolynomialNorm L n ≠ 0)
    (hhprev : orthogonalPolynomialNorm L (n - 1) ≠ 0) :
    HasDerivAt (fun t : ℝ => orthogonalRecurrenceBeta (L + t • D) n)
      (D (orthogonalRecurrenceBetaSensitivityPolynomial L n)) 0 := by
  have hL : ∀ k, ContDiffAt ℝ 1 (fun t : ℝ => (L + t • D) (X ^ k)) 0 := by
    intro k
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    exact contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)
  have hD : ∀ k, HasDerivAt (fun t : ℝ => (L + t • D) (X ^ k)) (D (X ^ k)) 0 := by
    intro k
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    convert (hasDerivAt_const 0 (L (X ^ k))).fun_add
      ((hasDerivAt_id 0).mul_const (D (X ^ k))) using 1
    all_goals first | rfl | simp
  simpa only [zero_smul, add_zero] using hasDerivAt_orthogonalRecurrenceBeta hn0 hL hD
    (by simpa only [zero_smul, add_zero] using hn)
    (by simpa only [zero_smul, add_zero] using hprev)
    (by simpa only [zero_smul, add_zero] using hh)
    (by simpa only [zero_smul, add_zero] using hhprev)

end NLAlib
