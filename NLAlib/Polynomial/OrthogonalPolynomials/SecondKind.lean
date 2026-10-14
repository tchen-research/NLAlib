import NLAlib.Polynomial.OrthogonalPolynomials.Recurrence
import NLAlib.ForMathlib.Algebra.PolynomialDividedDifference

/-! # Second-kind polynomials from finite moment recurrences

The second-kind numerator is defined by a finite polynomial recurrence.
Applying the moment functional to the exact divided-difference polynomial
gives the same numerator, so no pointwise singular quotient is integrated.
Source: Gautschi (2004), Chapter 1; operator derivations AQ16–AQ17.
-/

noncomputable section

open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- The second-kind numerator, with zero order zero and mass at order one.
The recurrence is total; its moment interpretation requires finite Hankel
nondegeneracy through the requested order. -/
def secondKindPolynomial (L : 𝕜[X] →ₗ[𝕜] 𝕜) : ℕ → 𝕜[X]
  | 0 => 0
  | 1 => C (L 1)
  | n + 2 => (X - C (orthogonalRecurrenceAlpha L (n + 1))) * secondKindPolynomial L (n + 1) -
      C (orthogonalRecurrenceBeta L (n + 1)) * secondKindPolynomial L n

/-- The second-kind numerator at order zero is zero.
atlas: jacobi-fraction-second-kind (partial) -/
@[simp] theorem secondKindPolynomial_zero (L : 𝕜[X] →ₗ[𝕜] 𝕜) :
    secondKindPolynomial L 0 = 0 := rfl

/-- The first second-kind numerator is the constant mass.
atlas: jacobi-fraction-second-kind (partial) -/
@[simp] theorem secondKindPolynomial_one (L : 𝕜[X] →ₗ[𝕜] 𝕜) :
    secondKindPolynomial L 1 = C (L 1) := rfl

/-- Positive-order second-kind numerators satisfy the original monic
recurrence. Source: Gautschi (2004), Chapter 1, AQ17.
atlas: jacobi-fraction-second-kind (partial) -/
theorem secondKindPolynomial_add_two (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    secondKindPolynomial L (n + 2) =
      (X - C (orthogonalRecurrenceAlpha L (n + 1))) * secondKindPolynomial L (n + 1) -
        C (orthogonalRecurrenceBeta L (n + 1)) * secondKindPolynomial L n := rfl

/-- The second-kind numerator has degree at most one less than its order.
atlas: jacobi-fraction-second-kind (partial) -/
theorem natDegree_secondKindPolynomial_le (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    (secondKindPolynomial L n).natDegree ≤ n - 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih1 =>
    rw [secondKindPolynomial_add_two]
    have hleft : ((X - C (orthogonalRecurrenceAlpha L (n + 1))) *
        secondKindPolynomial L (n + 1)).natDegree ≤ n + 1 := by
      apply (natDegree_mul_le).trans
      rw [natDegree_X_sub_C]
      omega
    have hright : (C (orthogonalRecurrenceBeta L (n + 1)) *
        secondKindPolynomial L n).natDegree ≤ n + 1 :=
      (natDegree_C_mul_le _ _).trans (ih.trans (by omega))
    exact (natDegree_sub_le _ _).trans (by simpa using max_le hleft hright)

private theorem functional_dividedDifference_recurrence
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hL : ∀ k ≤ n + 2, hankelMomentDet L k ≠ 0) (z : 𝕜) :
    L ((monicOrthogonalPolynomial L (n + 2)).dividedDifference z) =
      (z - orthogonalRecurrenceAlpha L (n + 1)) *
        L ((monicOrthogonalPolynomial L (n + 1)).dividedDifference z) -
      orthogonalRecurrenceBeta L (n + 1) *
        L ((monicOrthogonalPolynomial L n).dividedDifference z) := by
  let p := monicOrthogonalPolynomial L (n + 1)
  let d := p.dividedDifference z
  have hC (c : 𝕜) : L (C c) = c * L 1 := by
    rw [show C c = c • (1 : 𝕜[X]) by rw [← C_mul', mul_one], map_smul]
    rfl
  have hfactor := congrArg L (X_sub_C_mul_dividedDifference p z)
  rw [sub_mul, map_sub, C_mul', map_smul, map_sub, hC] at hfactor
  simp only [smul_eq_mul] at hfactor
  have hzero : L p = 0 := by
    have hp := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL (n + 1) (by omega))
    simpa only [mul_one] using hp.orthogonal 1
      (by rw [degree_one]; exact_mod_cast (Nat.zero_lt_succ n))
  rw [monicOrthogonalPolynomial_succ_eq L (n + 1) hL, sub_mul,
    dividedDifference_sub, dividedDifference_sub, dividedDifference_X_mul,
    dividedDifference_C_mul, dividedDifference_C_mul]
  simp only [Nat.add_sub_cancel, map_sub, map_add, C_mul', map_smul, smul_eq_mul, hC]
  change L (X * d) + p.eval z * L 1 - orthogonalRecurrenceAlpha L (n + 1) * L d -
    orthogonalRecurrenceBeta L (n + 1) *
      L ((monicOrthogonalPolynomial L n).dividedDifference z) = _
  rw [hzero] at hfactor
  linear_combination hfactor

/-- The second-kind numerator is exactly the moment-functional divided
difference, including diagonal values interpreted polynomially.
Source: Gautschi (2004), Chapter 1, AQ16–AQ17.
atlas: jacobi-fraction-second-kind (partial) -/
theorem eval_secondKindPolynomial_eq_functional_dividedDifference
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0) (z : 𝕜) :
    (secondKindPolynomial L n).eval z =
      L ((monicOrthogonalPolynomial L n).dividedDifference z) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have hr := monicOrthogonalPolynomial_succ_eq L 0 hL
    simp [orthogonalRecurrenceBeta] at hr
    rw [secondKindPolynomial_one, eval_C, hr, dividedDifference_sub,
      dividedDifference_X, dividedDifference_C]
    simp
  | more n ih ih1 =>
    rw [secondKindPolynomial_add_two, eval_sub, eval_mul, eval_sub, eval_X, eval_C,
      eval_mul, eval_C, ih1 (fun k hk => hL k (by omega)), ih (fun k hk => hL k (by omega))]
    exact (functional_dividedDifference_recurrence L n hL z).symm

/-- Any exact distinct-node rule whose nodes are roots of the canonical monic
polynomial gives the finite second-kind partial fraction. The numerator/denominator
ratio needs only its final denominator and the stated node differences nonzero.
Source: Gautschi (2004), Chapter 1, AQ18.
atlas: jacobi-fraction-second-kind (partial) -/
theorem eval_secondKindPolynomial_div_eq_sum_weight_div
    {ι : Type*} [Fintype ι] (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hn : 0 < n)
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0) (v w : ι → 𝕜)
    (hv : ∀ i, (monicOrthogonalPolynomial L n).eval (v i) = 0)
    (hexact : ∀ p : 𝕜[X], p.degree < n → L p = ∑ i, w i * p.eval (v i))
    {z : 𝕜} (hz : (monicOrthogonalPolynomial L n).eval z ≠ 0)
    (hzv : ∀ i, z ≠ v i) :
    (secondKindPolynomial L n).eval z / (monicOrthogonalPolynomial L n).eval z =
      ∑ i, w i / (z - v i) := by
  rw [eval_secondKindPolynomial_eq_functional_dividedDifference L n hL z,
    hexact _ (degree_dividedDifference_lt hn
      (by rw [natDegree_monicOrthogonalPolynomial]) z), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_dividedDifference_of_ne _ (fun h => hzv i h.symm), hv i]
  field_simp [hz, sub_ne_zero.mpr (hzv i), sub_ne_zero.mpr (fun h => hzv i h.symm)]
  ring

/-- Applying an exact rule to the divided difference gives a polynomial
identity for the numerator, including all diagonal values. -/
theorem secondKindPolynomial_eq_sum_weight_mul_dividedDifference
    [Infinite 𝕜] {ι : Type*} [Fintype ι] (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hn : 0 < n)
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0) (v w : ι → 𝕜)
    (hexact : ∀ p : 𝕜[X], p.degree < n → L p = ∑ i, w i * p.eval (v i)) :
    secondKindPolynomial L n =
      ∑ i, C (w i) * (monicOrthogonalPolynomial L n).dividedDifference (v i) := by
  apply Polynomial.funext
  intro z
  rw [eval_secondKindPolynomial_eq_functional_dividedDifference L n hL z,
    hexact _ (degree_dividedDifference_lt hn
      (by rw [natDegree_monicOrthogonalPolynomial]) z)]
  simp only [eval_finsetSum, eval_mul, eval_C]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_dividedDifference_comm]

/-- At a simple rule node the second-kind numerator is its weight times the
derivative of the monic denominator. Source: Gautschi (2004), Chapter 1, AQ18.
atlas: jacobi-fraction-second-kind (partial) -/
theorem eval_secondKindPolynomial_at_node
    {ι : Type*} [Fintype ι] [DecidableEq ι] (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hn : 0 < n)
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0) (v w : ι → 𝕜) (hv : Function.Injective v)
    (hroot : ∀ i, (monicOrthogonalPolynomial L n).eval (v i) = 0)
    (hexact : ∀ p : 𝕜[X], p.degree < n → L p = ∑ i, w i * p.eval (v i)) (i : ι) :
    (secondKindPolynomial L n).eval (v i) =
      w i * (monicOrthogonalPolynomial L n).derivative.eval (v i) := by
  rw [eval_secondKindPolynomial_eq_functional_dividedDifference L n hL (v i),
    hexact _ (degree_dividedDifference_lt hn
      (by rw [natDegree_monicOrthogonalPolynomial]) (v i))]
  rw [Finset.sum_eq_single i]
  · rw [eval_dividedDifference_self]
  · intro j _ hji
    rw [eval_dividedDifference_of_ne _ (fun h => hji (hv h)), hroot j, hroot i]
    simp
  · simp

/-- The numerator partial fraction persists under a field extension, so a
real moment functional gives the same ratio at complex arguments without
replacing its bilinear convention by a Hermitian inner product.
Source: Gautschi (2004), Chapter 1, AQ18.
atlas: jacobi-fraction-second-kind (partial) -/
theorem eval_map_secondKindPolynomial_div_eq_sum_weight_div
    [Infinite 𝕜] {𝕜' : Type*} [Field 𝕜'] {ι : Type*} [Fintype ι]
    (f : 𝕜 →+* 𝕜') (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) (hn : 0 < n)
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0) (v w : ι → 𝕜)
    (hv : ∀ i, (monicOrthogonalPolynomial L n).eval (v i) = 0)
    (hexact : ∀ p : 𝕜[X], p.degree < n → L p = ∑ i, w i * p.eval (v i))
    {z : 𝕜'} (hz : ((monicOrthogonalPolynomial L n).map f).eval z ≠ 0)
    (hzv : ∀ i, z ≠ f (v i)) :
    ((secondKindPolynomial L n).map f).eval z /
        ((monicOrthogonalPolynomial L n).map f).eval z =
      ∑ i, f (w i) / (z - f (v i)) := by
  rw [secondKindPolynomial_eq_sum_weight_mul_dividedDifference L n hn hL v w hexact,
    Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_C, eval_finsetSum, eval_mul, eval_C]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun p : 𝕜[X] => (p.map f).eval z)
    (X_sub_C_mul_dividedDifference (monicOrthogonalPolynomial L n) (v i))
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    eval_mul, eval_sub, eval_X, eval_C, hv i, map_zero, sub_zero] at h
  have hdd : (((monicOrthogonalPolynomial L n).dividedDifference (v i)).map f).eval z =
      ((monicOrthogonalPolynomial L n).map f).eval z / (z - f (v i)) := by
    apply (eq_div_iff (sub_ne_zero.mpr (hzv i))).mpr
    simpa only [mul_comm] using h
  rw [hdd]
  field_simp

end NLAlib
