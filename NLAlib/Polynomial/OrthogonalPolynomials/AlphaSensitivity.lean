import NLAlib.Polynomial.OrthogonalPolynomials.OrthogonalitySensitivity
import NLAlib.Polynomial.OrthogonalPolynomials.Recurrence
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Moment sensitivity of monic diagonal coefficients

The polynomial quotient rule, differentiated lower-degree orthogonality, and the
three-term recurrence give the exact monic sensitivity polynomial. This form uses
only moments through degree `2n+1`, without normalizing the next polynomial.
Source: Gautschi (2004), §2.1; AQ29–AQ30 in the operator re-derivations.
-/

noncomputable section
open Polynomial
namespace NLAlib

set_option backward.isDefEq.respectTransparency false

/-- The monic sensitivity polynomial of a diagonal recurrence coefficient.
The previous-order term vanishes at order zero because the boundary beta is zero. -/
def orthogonalRecurrenceAlphaSensitivityPolynomial (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) : ℝ[X] :=
  C (orthogonalPolynomialNorm L n)⁻¹ *
    ((X - C (orthogonalRecurrenceAlpha L n)) * monicOrthogonalPolynomial L n ^ 2 -
      C (2 * orthogonalRecurrenceBeta L n) *
        (monicOrthogonalPolynomial L (n - 1) * monicOrthogonalPolynomial L n))

/-- The equivalent adjacent-polynomial form of the diagonal sensitivity uses
no normalization of the next order. Source: AQ30; the previous term is omitted
at order zero.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem orthogonalRecurrenceAlphaSensitivityPolynomial_eq_adjacent
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ}
    (hn : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0)
    (hh : orthogonalPolynomialNorm L n ≠ 0)
    (hprev : n ≠ 0 → orthogonalPolynomialNorm L (n - 1) ≠ 0) :
    orthogonalRecurrenceAlphaSensitivityPolynomial L n =
      C (orthogonalPolynomialNorm L n)⁻¹ *
        (monicOrthogonalPolynomial L n * monicOrthogonalPolynomial L (n + 1)) -
      if n = 0 then 0 else C (orthogonalPolynomialNorm L (n - 1))⁻¹ *
        (monicOrthogonalPolynomial L (n - 1) * monicOrthogonalPolynomial L n) := by
  rw [monicOrthogonalPolynomial_succ_eq L n hn]
  by_cases hn0 : n = 0
  · subst n
    simp only [orthogonalRecurrenceAlphaSensitivityPolynomial,
      orthogonalRecurrenceBeta, ite_true, mul_zero, map_zero, zero_mul, sub_zero]
    ring
  · simp only [orthogonalRecurrenceAlphaSensitivityPolynomial,
      orthogonalRecurrenceBeta, if_neg hn0, map_mul, map_ofNat]
    have hcancel : C (orthogonalPolynomialNorm L n)⁻¹ *
        C (orthogonalPolynomialNorm L n / orthogonalPolynomialNorm L (n - 1)) =
        C (orthogonalPolynomialNorm L (n - 1))⁻¹ := by
      rw [← map_mul]
      congr 1
      field_simp
    linear_combination - (monicOrthogonalPolynomial L (n - 1) *
      monicOrthogonalPolynomial L n) * hcancel

private theorem functional_X_mul_monic_mul_variation_eq
    {L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)} {D : ℝ[X] →ₗ[ℝ] ℝ} {n : ℕ} {x : ℝ}
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hD : ∀ k, HasDerivAt (fun y => L y (X ^ k)) (D (X ^ k)) x)
    (hn : ∀ k ≤ n + 1, hankelMomentDet (L x) k ≠ 0) :
    L x (X * monicOrthogonalPolynomial (L x) n * monicOrthogonalPolynomialDeriv L n x) =
      -orthogonalRecurrenceBeta (L x) n *
        D (monicOrthogonalPolynomial (L x) n * monicOrthogonalPolynomial (L x) (n - 1)) := by
  let P := monicOrthogonalPolynomial (L x)
  let V := monicOrthogonalPolynomialDeriv L n x
  have hV : V.degree < n := degree_monicOrthogonalPolynomialDeriv_lt L n x
  by_cases hn0 : n = 0
  · subst n
    have hVz : V = 0 := by simp [V, monicOrthogonalPolynomialDeriv]
    simp [V, hVz, orthogonalRecurrenceBeta]
  · have hrec := monicOrthogonalPolynomial_succ_eq (L x) n hn
    have heq : X * P n = P (n + 1) + C (orthogonalRecurrenceAlpha (L x) n) * P n +
        C (orthogonalRecurrenceBeta (L x) n) * P (n - 1) := by
      dsimp only [P]
      linear_combination -hrec
    have horth := (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (L x)
      (hn n (by omega))).orthogonal V hV
    have horthnext := (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (L x)
      (hn (n + 1) le_rfl)).orthogonal V (hV.trans (by exact_mod_cast Nat.lt_succ_self n))
    have hprev : (P (n - 1)).degree < n := by
      rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial (L x) _).ne_zero,
        natDegree_monicOrthogonalPolynomial]
      exact_mod_cast (show n - 1 < n by omega)
    have hvar := functional_monicOrthogonalPolynomialDeriv_mul_eq_neg hL hD
      (hn n (by omega)) hprev
    change L x (X * P n * V) = _
    rw [heq, add_mul, add_mul, map_add, map_add, mul_assoc, C_mul', map_smul,
      mul_assoc, C_mul', map_smul, horthnext, horth, smul_zero, zero_add, zero_add]
    rw [mul_comm (P (n - 1)) V, hvar]
    simp only [smul_eq_mul]
    ring

/-- The actual first derivative of the diagonal recurrence coefficient is the
moment variation evaluated at its sensitivity polynomial. Source: AQ29–AQ30.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem hasDerivAt_orthogonalRecurrenceAlpha
    {L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)} {D : ℝ[X] →ₗ[ℝ] ℝ} {n : ℕ} {x : ℝ}
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hD : ∀ k, HasDerivAt (fun y => L y (X ^ k)) (D (X ^ k)) x)
    (hn : ∀ k ≤ n + 1, hankelMomentDet (L x) k ≠ 0)
    (hh : orthogonalPolynomialNorm (L x) n ≠ 0) :
    HasDerivAt (fun y => orthogonalRecurrenceAlpha (L y) n)
      (D (orthogonalRecurrenceAlphaSensitivityPolynomial (L x) n)) x := by
  let P := fun y => monicOrthogonalPolynomial (L y) n
  let V := monicOrthogonalPolynomialDeriv L n x
  have hP := hasPolynomialDerivAt_monicOrthogonalPolynomial hL (hn n (by omega))
  have hV : V.degree ≤ n := (degree_monicOrthogonalPolynomialDeriv_lt L n x).le
  have hPdeg (y : ℝ) : (P y).degree = n := by
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial (L y) n).ne_zero,
      natDegree_monicOrthogonalPolynomial]
  have hBdeg : (X * (V * P x + P x * V)).degree < ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    apply (degree_mul_le _ _).trans_lt
    rw [degree_X]
    have hsum : (V * P x + P x * V).degree ≤ (n : WithBot ℕ) + n := by
      apply (degree_add_le _ _).trans
      apply max_le
      · exact (degree_mul_le _ _).trans (by rw [hPdeg]; exact add_le_add hV le_rfl)
      · exact (degree_mul_le _ _).trans (by rw [hPdeg]; exact add_le_add le_rfl hV)
    apply (add_le_add (le_rfl : (1 : WithBot ℕ) ≤ 1) hsum).trans_lt
    exact_mod_cast (show 1 + (n + n) < 2 * n + 2 by omega)
  have hpoly := (hasCoeffDerivAt_const X x).mul (hP.mul hP)
  simp only [zero_mul, zero_add] at hpoly
  have hnum := hasDerivAt_functional_polynomial (d := 2 * n + 2)
    (p := fun y => X * (P y * P y)) (p' := X * (V * P x + P x * V))
    (by intro y; rw [degree_mul, degree_X, degree_mul, hPdeg];
        exact_mod_cast (show 1 + (n + n) < 2 * n + 2 by omega)) hBdeg hpoly hD
  have hcross := functional_X_mul_monic_mul_variation_eq hL hD hn
  have hB : X * (V * P x + P x * V) = C (2 : ℝ) * (X * P x * V) := by
    simp only [map_ofNat]
    ring
  have hBvalue : L x (X * (V * P x + P x * V)) =
      -2 * orthogonalRecurrenceBeta (L x) n *
        D (monicOrthogonalPolynomial (L x) n * monicOrthogonalPolynomial (L x) (n - 1)) := by
    rw [hB, C_mul', map_smul, hcross]
    simp only [smul_eq_mul]
    ring
  rw [hBvalue] at hnum
  have h := hnum.fun_div (hasDerivAt_orthogonalPolynomialNorm hL hD (hn n (by omega))) hh
  have heq : D (orthogonalRecurrenceAlphaSensitivityPolynomial (L x) n) =
      ((D (X * (P x * P x)) +
          -2 * orthogonalRecurrenceBeta (L x) n *
            D (monicOrthogonalPolynomial (L x) n * monicOrthogonalPolynomial (L x) (n - 1))) *
          orthogonalPolynomialNorm (L x) n -
        L x (X * (P x * P x)) * D (monicOrthogonalPolynomial (L x) n ^ 2)) /
          orthogonalPolynomialNorm (L x) n ^ 2 := by
    simp only [orthogonalRecurrenceAlphaSensitivityPolynomial, mul_sub, map_sub,
      C_mul', map_smul, sub_mul, smul_eq_mul, mul_comm (monicOrthogonalPolynomial (L x) (n - 1))]
    simp only [orthogonalRecurrenceAlpha, P, pow_two]
    field_simp
    ring
  rw [heq]
  convert h using 1
  all_goals first | rfl | simp only [orthogonalRecurrenceAlpha, P, pow_two]

/-- Affine perturbation of a moment functional gives the exact diagonal
directional derivative, without smoothness or derivative hypotheses for the
perturbation itself. A coordinate derivative follows by taking `D` to be the
fixed-basis dual coordinate functional. Source: AQ29–AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem hasDerivAt_orthogonalRecurrenceAlpha_affine
    (L D : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ)
    (hn : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0)
    (hh : orthogonalPolynomialNorm L n ≠ 0) :
    HasDerivAt (fun t : ℝ => orthogonalRecurrenceAlpha (L + t • D) n)
      (D (orthogonalRecurrenceAlphaSensitivityPolynomial L n)) 0 := by
  have hL : ∀ k, ContDiffAt ℝ 1 (fun t : ℝ => (L + t • D) (X ^ k)) 0 := by
    intro k
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    exact (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const))
  have hD : ∀ k, HasDerivAt (fun t : ℝ => (L + t • D) (X ^ k)) (D (X ^ k)) 0 := by
    intro k
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    convert (hasDerivAt_const 0 (L (X ^ k))).fun_add
      ((hasDerivAt_id 0).mul_const (D (X ^ k))) using 1
    all_goals first | rfl | simp
  simpa only [zero_smul, add_zero] using hasDerivAt_orthogonalRecurrenceAlpha hL hD
    (by simpa only [zero_smul, add_zero] using hn)
    (by simpa only [zero_smul, add_zero] using hh)

end NLAlib
