import NLAlib.Polynomial.OrthogonalPolynomials.HankelNorms
import NLAlib.Polynomial.OrthogonalPolynomials.CoefficientIdentities
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Bordered and shifted Hankel determinants

The finite orthogonality system gives a bordered determinant representation of
the monic polynomial. Replacing the final column of the finite Hankel matrix
gives its next coefficient, and hence the diagonal recurrence coefficient.
All formulas are bilinear over an arbitrary field.
Source: Gautschi (2004), Chapter 1; operator derivations (OF4)--(OF6).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix Finset
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜]

/-- The shifted determinant `E_n` uses moment columns `0,...,n-2,n`, with
rows `0,...,n-1`. The order-zero convention is zero.
Source: operator derivations (OF4)--(OF6). -/
def shiftedHankelMomentDet (L : 𝕜[X] →ₗ[𝕜] 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n+1 => ((hankelMomentMatrix L (n+1)).updateCol (Fin.last n)
      (fun i => L (X ^ ((n+1) + i.val)))).det

@[simp] theorem shiftedHankelMomentDet_zero (L : 𝕜[X] →ₗ[𝕜] 𝕜) :
    shiftedHankelMomentDet L 0 = 0 := rfl

private theorem coeff_monicOrthogonalPolynomial_below (L : 𝕜[X] →ₗ[𝕜] 𝕜)
    {n : ℕ} (i : Fin n) :
    (monicOrthogonalPolynomial L n).coeff i.val = orthogonalPolynomialCoefficients L n i := by
  unfold monicOrthogonalPolynomial orthogonalPolynomialLowerPart
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt),
    coeff_sum_monomial_fin, zero_add]

/-- The next coefficient of the monic moment-system polynomial is the negative
shifted determinant quotient. Order zero uses `E_0=0` and `nextCoeff 1=0`.
Only the order-`n` Hankel system must be nonsingular.
Source: operator derivations (OF4)--(OF6).
atlas: formal-orthogonal-polynomials (partial), monic-orthogonal-recurrence (partial), hankel-moment-positivity (partial) -/
theorem nextCoeff_monicOrthogonalPolynomial_eq_neg_shiftedHankelMomentDet_div
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hn : hankelMomentDet L n ≠ 0) :
    (monicOrthogonalPolynomial L n).nextCoeff =
      -shiftedHankelMomentDet L n / hankelMomentDet L n := by
  cases n with
  | zero =>
    simp only [monicOrthogonalPolynomial_zero, shiftedHankelMomentDet_zero,
      hankelMomentDet_zero, neg_zero, zero_div]
    simpa only [C_1] using nextCoeff_C_eq_zero (1 : 𝕜)
  | succ n =>
    rw [nextCoeff_of_natDegree_pos (by rw [natDegree_monicOrthogonalPolynomial]; omega),
      natDegree_monicOrthogonalPolynomial, Nat.add_sub_cancel]
    rw [show n = (Fin.last n).val by rfl, coeff_monicOrthogonalPolynomial_below,
      orthogonalPolynomialCoefficients]
    simp only [Fin.val_last]
    have h := congrFun (det_smul_inv_mulVec_eq_cramer (hankelMomentMatrix L (n+1))
      (fun i => L (X ^ ((n+1)+i.val))) (isUnit_iff_ne_zero.mpr hn)) (Fin.last n)
    change (hankelMomentMatrix L (n+1)).det *
      ((hankelMomentMatrix L (n+1))⁻¹ *ᵥ (fun i => L (X ^ ((n+1)+i.val)))) (Fin.last n) =
      ((hankelMomentMatrix L (n+1)).updateCol (Fin.last n)
        (fun i => L (X ^ ((n+1)+i.val)))).det at h
    rw [show (fun i : Fin (n+1) => -L (X ^ ((n+1)+i.val))) =
      -(fun i : Fin (n+1) => L (X ^ ((n+1)+i.val))) by rfl,
      mulVec_neg, Pi.neg_apply]
    change -_ = -_ / (hankelMomentMatrix L (n+1)).det
    apply (eq_div_iff hn).mpr
    simp only [hankelMomentDet, shiftedHankelMomentDet]
    linear_combination -h

/-- The diagonal monic recurrence coefficient is the difference of consecutive
shifted Hankel determinant quotients. The finite leading systems through `n+1`
are assumed nonsingular, so every displayed denominator is nonzero.
Source: operator derivations (OF6).
atlas: monic-orthogonal-recurrence (partial), hankel-moment-positivity (partial) -/
theorem orthogonalRecurrenceAlpha_eq_shiftedHankelMomentDet_sub
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ)
    (hL : ∀ k ≤ n+1, hankelMomentDet L k ≠ 0) :
    orthogonalRecurrenceAlpha L n =
      shiftedHankelMomentDet L (n+1) / hankelMomentDet L (n+1) -
        shiftedHankelMomentDet L n / hankelMomentDet L n := by
  rw [orthogonalRecurrenceAlpha_eq_sub_nextCoeff L n hL,
    nextCoeff_monicOrthogonalPolynomial_eq_neg_shiftedHankelMomentDet_div L n
      (hL n (by omega)),
    nextCoeff_monicOrthogonalPolynomial_eq_neg_shiftedHankelMomentDet_div L (n+1)
      (hL (n+1) le_rfl)]
  ring

/-- The bordered Hankel matrix with moment rows followed by the polynomial
row `1,X,...,X^n`. Sum labels put the last row and column after `Fin n`.
Source: operator derivations (OF4). -/
def borderedHankelMatrix (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) 𝕜[X] :=
  fromBlocks ((hankelMomentMatrix L n).map C)
    (fun i _ => C (L (X ^ (n+i.val))))
    (fun _ j => X ^ j.val) (fun _ _ => X ^ n)

/-- The bordered Hankel determinant equals the ordinary Hankel determinant
times its monic moment-system polynomial, including the empty order-zero system.
Source: operator derivations (OF4).
atlas: formal-orthogonal-polynomials (partial), hankel-moment-positivity (partial) -/
theorem det_borderedHankelMatrix_eq (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ)
    (hn : hankelMomentDet L n ≠ 0) :
    (borderedHankelMatrix L n).det =
      C (hankelMomentDet L n) * monicOrthogonalPolynomial L n := by
  let H := hankelMomentMatrix L n
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hn
  let : Invertible (H.map C) :=
    { invOf := (H⁻¹).map C
      invOf_mul_self := by rw [← Matrix.map_mul, H.nonsing_inv_mul hunit]; simp
      mul_invOf_self := by rw [← Matrix.map_mul, H.mul_nonsing_inv hunit]; simp }
  rw [borderedHankelMatrix, det_fromBlocks₁₁, det_eq_elem_of_subsingleton _ (0 : Fin 1)]
  have hdet : (H.map C).det = C H.det := (RingHom.map_det C H).symm
  rw [hdet]
  congr 1
  change X^n - (∑ j : Fin n,
      (∑ i : Fin n, (X : 𝕜[X])^i.val * C (H⁻¹ i j)) * C (L (X ^ (n+j.val)))) =
    monicOrthogonalPolynomial L n
  rw [monicOrthogonalPolynomial, orthogonalPolynomialLowerPart]
  simp only [sum_mul]
  rw [sum_comm]
  have hterms (i : Fin n) :
      (∑ j : Fin n, (X : 𝕜[X])^i.val * C (H⁻¹ i j) * C (L (X ^ (n+j.val)))) =
        -monomial i.val (orthogonalPolynomialCoefficients L n i) := by
    rw [orthogonalPolynomialCoefficients]
    change _ = -monomial i.val ((H⁻¹ *ᵥ (fun j => -L (X ^ (n+j.val)))) i)
    simp only [mulVec, dotProduct,
      mul_neg, sum_neg_distrib, monomial_neg, neg_neg]
    rw [← C_mul_X_pow_eq_monomial, mul_comm]
    rw [map_sum, mul_sum]
    apply sum_congr rfl
    intro j _
    rw [map_mul, mul_assoc]
  simp_rw [hterms]
  rw [sum_neg_distrib, sub_neg_eq_add]

/-- The monic moment-system polynomial is the bordered Hankel determinant
divided by the ordinary Hankel determinant. This includes order zero, where
the bordered determinant and the monic polynomial are both one.
Source: operator derivations (OF4).
atlas: formal-orthogonal-polynomials (partial), hankel-moment-positivity (partial) -/
theorem monicOrthogonalPolynomial_eq_inv_smul_det_borderedHankelMatrix
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hn : hankelMomentDet L n ≠ 0) :
    monicOrthogonalPolynomial L n =
      (hankelMomentDet L n)⁻¹ • (borderedHankelMatrix L n).det := by
  rw [det_borderedHankelMatrix_eq L n hn, smul_eq_C_mul, ← mul_assoc,
    ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul]

@[simp] theorem det_borderedHankelMatrix_zero (L : 𝕜[X] →ₗ[𝕜] 𝕜) :
    (borderedHankelMatrix L 0).det = 1 := by
  rw [det_borderedHankelMatrix_eq L 0 (by simp), hankelMomentDet_zero,
    monicOrthogonalPolynomial_zero, map_one, one_mul]

end NLAlib
