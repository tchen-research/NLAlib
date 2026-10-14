import Mathlib.Algebra.Polynomial.SumIteratedDerivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Classical Laguerre polynomials and finite exponential moments

The exponential moment functional is defined by its finite monomial moments.
The Rodrigues operator `D - I` gives the classical normalization of Laguerre
polynomials. All orthogonality arguments are finite polynomial identities.
Source: the reciprocal exponential certificate (RC1)--(RC8) in the operator
re-derivations, and the classical Laguerre Rodrigues formula.
-/

noncomputable section
open Polynomial
open scoped Nat
namespace NLAlib

/-- The polynomial moment functional with moments `r! / s^(r+1)`.
For positive `s` these are the moments of `exp (-s*x)` on the positive half-line.
Source: reciprocal exponential certificate (RC5). -/
def exponentialPolynomialMoment (s : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun r => ((r ! : ℝ) / s ^ (r + 1)) • LinearMap.id

@[simp] theorem exponentialPolynomialMoment_monomial (s a : ℝ) (r : ℕ) :
    exponentialPolynomialMoment s (monomial r a) = a * (r ! : ℝ) / s ^ (r + 1) := by
  simp [exponentialPolynomialMoment, Polynomial.lsum_apply,
    Polynomial.sum_monomial_index, mul_comm, mul_div_assoc]

@[simp] theorem exponentialPolynomialMoment_X_pow (s : ℝ) (r : ℕ) :
    exponentialPolynomialMoment s (X ^ r) = (r ! : ℝ) / s ^ (r + 1) := by
  simpa only [monomial_one_right_eq_X_pow, one_mul] using
    exponentialPolynomialMoment_monomial s 1 r

@[simp] theorem exponentialPolynomialMoment_C (s a : ℝ) :
    exponentialPolynomialMoment s (C a) = a / s := by
  simpa using exponentialPolynomialMoment_monomial s a 0

/-- Finite integration by parts for the exponential moment functional.
Source: reciprocal exponential certificate (RC4)--(RC5). -/
theorem exponentialPolynomialMoment_derivative {s : ℝ} (hs : s ≠ 0) (p : ℝ[X]) :
    exponentialPolynomialMoment s p.derivative =
      s * exponentialPolynomialMoment s p - p.coeff 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, coeff_add, hp, hq]
    ring
  | monomial n a =>
    cases n with
    | zero => simp; field_simp; ring
    | succ n =>
      simp only [Polynomial.derivative_monomial, Nat.add_one_sub_one,
        exponentialPolynomialMoment_monomial, coeff_monomial, Nat.succ_ne_zero,
        if_false, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
      ring

/-- The finite Rodrigues operator for Laguerre polynomials, `D - I`.
Source: reciprocal exponential certificate (RC2). -/
def laguerreRodriguesOperator : ℝ[X] →ₗ[ℝ] ℝ[X] := derivative - LinearMap.id

@[simp] theorem laguerreRodriguesOperator_apply (p : ℝ[X]) :
    laguerreRodriguesOperator p = p.derivative - p := rfl

/-- The classical Laguerre polynomial `L_n`, normalized to have constant term one
and leading coefficient `(-1)^n/n!`. This finite Rodrigues definition equals
`exp x * D^n (exp (-x) * x^n) / n!`.
Source: reciprocal exponential certificate (RC1)--(RC2). -/
def laguerrePolynomial (n : ℕ) : ℝ[X] :=
  (n ! : ℝ)⁻¹ • (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n] (X ^ n)

private theorem X_pow_dvd_iterate_laguerreRodriguesOperator (n k : ℕ) :
    (X : ℝ[X]) ^ (n - k) ∣
      (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[k] (X ^ n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', laguerreRodriguesOperator_apply, Nat.sub_succ]
    exact (pow_sub_one_dvd_derivative_of_pow_dvd ih).sub
      ((pow_dvd_pow X (Nat.sub_le _ _)).trans ih)

private theorem coeff_zero_iterate_laguerreRodriguesOperator {n k : ℕ} (hk : k < n) :
    ((laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[k] (X ^ n)).coeff 0 = 0 := by
  apply X_dvd_iff.mp
  simpa only [pow_one] using (pow_dvd_pow X (by omega : 1 ≤ n - k)).trans
    (X_pow_dvd_iterate_laguerreRodriguesOperator n k)

private theorem derivative_commute_laguerreRodriguesOperator :
    Function.Commute (derivative : ℝ[X] → ℝ[X]) laguerreRodriguesOperator := by
  intro p
  simp [laguerreRodriguesOperator]

private theorem iterate_laguerreRodriguesOperator_zero (n : ℕ) :
    (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n] 0 = 0 :=
  iterate_map_zero laguerreRodriguesOperator n

private theorem iterate_laguerreRodriguesOperator_C (n : ℕ) (a : ℝ) :
    (laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[n] (C a) = C ((-1 : ℝ)^n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [laguerreRodriguesOperator_apply, derivative_C, zero_sub, ← C_neg, pow_succ]
    congr 1
    ring

/-- Applying `n` derivatives to `L_n` gives the constant `(-1)^n`.
Source: reciprocal exponential certificate (RC1). -/
theorem iterate_derivative_laguerrePolynomial_self (n : ℕ) :
    (derivative : ℝ[X] → ℝ[X])^[n] (laguerrePolynomial n) = C ((-1 : ℝ)^n) := by
  rw [laguerrePolynomial, iterate_derivative_smul]
  rw [(derivative_commute_laguerreRodriguesOperator.iterate_iterate n n) (X ^ n)]
  rw [iterate_derivative_X_pow_eq_natCast_mul, Nat.sub_self, pow_zero,
    mul_one, Nat.descFactorial_self, ← C_eq_natCast,
    iterate_laguerreRodriguesOperator_C, smul_C]
  simp only [smul_eq_mul]
  congr 1
  have hn : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- More than `n` derivatives annihilate the Laguerre polynomial of order `n`.
Source: reciprocal exponential certificate (RC1). -/
theorem iterate_derivative_laguerrePolynomial_eq_zero {n k : ℕ} (hnk : n < k) :
    (derivative : ℝ[X] → ℝ[X])^[k] (laguerrePolynomial n) = 0 := by
  rw [laguerrePolynomial, iterate_derivative_smul,
    (derivative_commute_laguerreRodriguesOperator.iterate_iterate k n) (X ^ n)]
  rw [iterate_derivative_eq_zero (by simpa using hnk),
    iterate_laguerreRodriguesOperator_zero, smul_zero]

private theorem exponentialPolynomialMoment_laguerreRodriguesOperator_mul
    (q p : ℝ[X]) :
    exponentialPolynomialMoment 1 (laguerreRodriguesOperator q * p) =
      -exponentialPolynomialMoment 1 (q * p.derivative) - q.coeff 0 * p.coeff 0 := by
  have h := exponentialPolynomialMoment_derivative (s := 1) one_ne_zero (q * p)
  rw [derivative_mul, map_add, one_mul, mul_coeff_zero] at h
  rw [laguerreRodriguesOperator_apply, sub_mul, map_sub]
  linarith

private theorem exponentialPolynomialMoment_iterate_laguerreRodriguesOperator_mul
    (n k : ℕ) (hk : k ≤ n) (p : ℝ[X]) :
    exponentialPolynomialMoment 1
      ((laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[k] (X ^ n) * p) =
      (-1 : ℝ)^k * exponentialPolynomialMoment 1
        (X ^ n * (derivative : ℝ[X] → ℝ[X])^[k] p) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',
      exponentialPolynomialMoment_laguerreRodriguesOperator_mul,
      coeff_zero_iterate_laguerreRodriguesOperator (by omega), zero_mul, sub_zero,
      ih (by omega), ← Function.iterate_succ_apply, pow_succ]
    ring

/-- Finite integration by parts for a classical Laguerre polynomial.
Source: reciprocal exponential certificate (RC4). -/
theorem exponentialPolynomialMoment_laguerrePolynomial_mul (n : ℕ) (p : ℝ[X]) :
    exponentialPolynomialMoment 1 (laguerrePolynomial n * p) =
      ((-1 : ℝ)^n / (n ! : ℝ)) * exponentialPolynomialMoment 1
        (X ^ n * (derivative : ℝ[X] → ℝ[X])^[n] p) := by
  rw [laguerrePolynomial, smul_mul_assoc, map_smul,
    exponentialPolynomialMoment_iterate_laguerreRodriguesOperator_mul n n le_rfl]
  simp only [smul_eq_mul]
  ring

/-- Classical Laguerre polynomials have unit diagonal and zero off-diagonal
exponential moments. This is the finite Gram identity, with no infinite expansion.
Source: reciprocal exponential certificate (RC6).
atlas: exp-rational-halfline (partial) -/
theorem exponentialPolynomialMoment_laguerrePolynomial_mul_laguerrePolynomial
    (i j : ℕ) :
    exponentialPolynomialMoment 1 (laguerrePolynomial i * laguerrePolynomial j) =
      if i = j then 1 else 0 := by
  obtain hij | rfl | hji := lt_trichotomy i j
  · rw [mul_comm, exponentialPolynomialMoment_laguerrePolynomial_mul,
      iterate_derivative_laguerrePolynomial_eq_zero hij, mul_zero, map_zero,
      mul_zero, if_neg (by omega)]
  · rw [exponentialPolynomialMoment_laguerrePolynomial_mul,
      iterate_derivative_laguerrePolynomial_self,
      show X ^ i * C ((-1 : ℝ)^i) = C ((-1 : ℝ)^i) * X ^ i by ring,
      ← smul_eq_C_mul,
      map_smul, exponentialPolynomialMoment_X_pow]
    simp only [smul_eq_mul, one_pow, div_one, ↓reduceIte]
    have hn : (i ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hsign : (-1 : ℝ)^i * (-1 : ℝ)^i = 1 := by
      rw [← mul_pow]
      norm_num
    field_simp
    simpa only [pow_two, ↓reduceIte] using hsign
  · rw [exponentialPolynomialMoment_laguerrePolynomial_mul,
      iterate_derivative_laguerrePolynomial_eq_zero hji, mul_zero, map_zero,
      mul_zero, if_neg (by omega)]

/-- The Laplace moment of a Laguerre polynomial is a finite geometric expression.
Source: reciprocal exponential certificate (RC3)--(RC6). -/
theorem exponentialPolynomialMoment_laguerrePolynomial {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    exponentialPolynomialMoment s (laguerrePolynomial n) =
      (s - 1)^n / s^(n + 1) := by
  have h (k : ℕ) (hk : k ≤ n) :
      exponentialPolynomialMoment s
        ((laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[k] (X ^ n)) =
        (s - 1)^k * exponentialPolynomialMoment s (X ^ n) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', laguerreRodriguesOperator_apply, map_sub,
        exponentialPolynomialMoment_derivative hs,
        coeff_zero_iterate_laguerreRodriguesOperator (by omega), sub_zero,
        ih (by omega), pow_succ]
      ring
  rw [laguerrePolynomial, map_smul, h n le_rfl, exponentialPolynomialMoment_X_pow]
  simp only [smul_eq_mul]
  have hn : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- The top coefficient of a classical Laguerre polynomial is `(-1)^n/n!`.
Source: reciprocal exponential certificate (RC1). -/
theorem coeff_laguerrePolynomial_self (n : ℕ) :
    (laguerrePolynomial n).coeff n = (-1 : ℝ)^n / (n ! : ℝ) := by
  have h := congrArg (fun p : ℝ[X] => p.coeff 0)
    (iterate_derivative_laguerrePolynomial_self n)
  simp only [coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul, coeff_C, ↓reduceIte] at h
  exact (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mpr (by
    simpa only [mul_comm] using h)

/-- Classical Laguerre polynomials have their prescribed degree, including order zero.
Source: reciprocal exponential certificate (RC1). -/
@[simp] theorem natDegree_laguerrePolynomial (n : ℕ) :
    (laguerrePolynomial n).natDegree = n := by
  have h (k : ℕ) :
      ((laguerreRodriguesOperator : ℝ[X] → ℝ[X])^[k] (X ^ n)).natDegree ≤ n := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', laguerreRodriguesOperator_apply]
      exact (natDegree_sub_le _ _).trans (max_le
        ((natDegree_derivative_le _).trans (Nat.sub_le _ _) |>.trans ih) ih)
  apply le_antisymm
  · exact (natDegree_smul_le _ _).trans (h n)
  · apply le_natDegree_of_ne_zero
    rw [coeff_laguerrePolynomial_self]
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero n)

/-- No classical Laguerre polynomial vanishes identically.
Source: reciprocal exponential certificate (RC1). -/
theorem laguerrePolynomial_ne_zero (n : ℕ) : laguerrePolynomial n ≠ 0 := by
  intro h
  have hh := coeff_laguerrePolynomial_self n
  rw [h, coeff_zero] at hh
  exact (div_ne_zero (pow_ne_zero _ (by norm_num))
    (by exact_mod_cast Nat.factorial_ne_zero n)) hh.symm

/-- The degree of a classical Laguerre polynomial equals its order.
Source: reciprocal exponential certificate (RC1). -/
@[simp] theorem degree_laguerrePolynomial (n : ℕ) :
    (laguerrePolynomial n).degree = n := by
  rw [degree_eq_natDegree (laguerrePolynomial_ne_zero n), natDegree_laguerrePolynomial]

/-- The Laguerre polynomials form a polynomial sequence in Mathlib's native sense.
Source: reciprocal exponential certificate (RC1), triangular basis. -/
def laguerrePolynomialSequence : Polynomial.Sequence ℝ where
  elems' := laguerrePolynomial
  degree_eq' := degree_laguerrePolynomial

/-- The first `n+1` classical Laguerre polynomials span the full degree-`n` space.
Source: reciprocal exponential certificate (RC1)--(RC6). -/
theorem span_laguerrePolynomial_eq_degreeLE (n : ℕ) :
    Submodule.span ℝ (Set.range (fun i : Fin (n + 1) => laguerrePolynomial i.val)) =
      degreeLE ℝ n := by
  have hset : Set.range (fun i : Fin (n + 1) => laguerrePolynomial i.val) =
      laguerrePolynomialSequence '' Set.Iic n := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by simpa using i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by simpa using hi⟩, rfl⟩
  rw [hset]
  apply Polynomial.Sequence.span_degreeLE
  intro i _
  apply isUnit_iff_ne_zero.mpr
  exact leadingCoeff_ne_zero.mpr (laguerrePolynomial_ne_zero i)

/-- Every degree-bounded polynomial is a finite Laguerre linear combination.
Source: reciprocal exponential certificate (RC6). -/
theorem exists_sum_smul_laguerrePolynomial {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n) :
    ∃ a : Fin (n + 1) → ℝ, p = ∑ i, a i • laguerrePolynomial i.val := by
  have hmem : p ∈ Submodule.span ℝ
      (Set.range (fun i : Fin (n + 1) => laguerrePolynomial i.val)) := by
    rw [span_laguerrePolynomial_eq_degreeLE]
    exact mem_degreeLE.mpr hp
  simpa only [eq_comm] using (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem

end NLAlib
