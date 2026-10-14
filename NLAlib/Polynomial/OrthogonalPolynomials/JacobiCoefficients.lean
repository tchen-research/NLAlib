import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMatrix
import NLAlib.Matrix.Structured.JacobiAlgebra

/-! # Actual Jacobi entries and monic coefficient squares

The compression definition has diagonal entries given by the monic norm quotient
and adjacent entries given by its positive square-root quotient. These identities
make the distinction between monic beta and normalized Jacobi off-diagonals explicit.
-/

noncomputable section
open Polynomial Matrix
open scoped Matrix

namespace NLAlib

/-- The actual moment Jacobi diagonal equals the monic recurrence alpha quotient.
Source: Gautschi (2004), Theorem 1.27; operator derivations (OF8).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial) -/
theorem orthogonalPolynomialJacobiMatrix_apply_self_eq_alpha (L : ℝ[X] →ₗ[ℝ] ℝ)
    {n : ℕ} (i : Fin n) (hH : 0 < orthogonalPolynomialNorm L i.val) :
    orthogonalPolynomialJacobiMatrix L n i i = orthogonalRecurrenceAlpha L i.val := by
  rw [orthogonalPolynomialJacobiMatrix, functional_X_orthonormalMomentPolynomial_mul,
    ← pow_two (Real.sqrt (orthogonalPolynomialNorm L i.val))⁻¹, inv_pow,
    Real.sq_sqrt hH.le, orthogonalRecurrenceAlpha]
  have hp : monicOrthogonalPolynomial L i.val * (X * monicOrthogonalPolynomial L i.val) =
      X * monicOrthogonalPolynomial L i.val ^ 2 := by ring
  rw [hp]
  ring

/-- The actual positive Jacobi off-diagonal is the square root of the monic
recurrence beta. Source: Gautschi (2004), Theorem 1.27; operator derivations (OF8).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial) -/
theorem orthogonalPolynomialJacobiMatrix_superdiagonal_eq_sqrt_beta
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    orthogonalPolynomialJacobiMatrix L n i j = Real.sqrt (orthogonalRecurrenceBeta L j.val) := by
  rw [orthogonalPolynomialJacobiMatrix, functional_X_orthonormalMomentPolynomial_mul]
  have hj := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL j.val j.isLt.le)
  rw [hj.functional_mul_eq_sq_of_monic (monic_X.mul (monic_monicOrthogonalPolynomial L i.val))
    (by rw [natDegree_X_mul (monic_monicOrthogonalPolynomial L i.val).ne_zero,
      natDegree_monicOrthogonalPolynomial]; omega)]
  rw [orthogonalRecurrenceBeta, if_neg (by omega : j.val ≠ 0),
    show j.val - 1 = i.val by omega, Real.sqrt_div (hH j.val j.isLt).le]
  change (Real.sqrt (orthogonalPolynomialNorm L j.val))⁻¹ *
      (Real.sqrt (orthogonalPolynomialNorm L i.val))⁻¹ * orthogonalPolynomialNorm L j.val = _
  field_simp [(Real.sqrt_pos.mpr (hH j.val j.isLt)).ne',
    (Real.sqrt_pos.mpr (hH i.val i.isLt)).ne']
  exact (Real.sq_sqrt (hH j.val j.isLt).le).symm

/-- Squaring the actual Jacobi off-diagonal gives the monic beta norm ratio.
Source: Gautschi (2004), Theorem 1.27; operator derivations (OF8).
atlas: monic-orthogonal-recurrence (partial) -/
theorem sq_orthogonalPolynomialJacobiMatrix_superdiagonal_eq_beta
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    orthogonalPolynomialJacobiMatrix L n i j ^ 2 = orthogonalRecurrenceBeta L j.val := by
  rw [orthogonalPolynomialJacobiMatrix_superdiagonal_eq_sqrt_beta L hL hH i j hij]
  apply Real.sq_sqrt
  rw [orthogonalRecurrenceBeta, if_neg (by omega : j.val ≠ 0), show j.val - 1 = i.val by omega]
  exact (div_pos (hH _ j.isLt) (hH _ i.isLt)).le

/-- Positive monic norms normalize the actual three-term recurrence, with square-root
off-diagonal coefficients and the zero boundary coefficient at order zero. The top
polynomial is normalized only under its explicit positive norm hypothesis.
Source: Gautschi (2004), Theorem 1.27; operator derivations (OF8).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial) -/
theorem X_mul_orthonormalMomentPolynomial (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ)
    (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0)
    (hH : ∀ k ≤ n + 1, 0 < orthogonalPolynomialNorm L k) :
    X * orthonormalMomentPolynomial L n =
      C (Real.sqrt (orthogonalRecurrenceBeta L n)) * orthonormalMomentPolynomial L (n - 1) +
      C (orthogonalRecurrenceAlpha L n) * orthonormalMomentPolynomial L n +
      C (Real.sqrt (orthogonalRecurrenceBeta L (n + 1))) * orthonormalMomentPolynomial L (n + 1) := by
  have hs (k : ℕ) (hk : k ≤ n + 1) : Real.sqrt (orthogonalPolynomialNorm L k) ≠ 0 :=
    (Real.sqrt_pos.mpr (hH k hk)).ne'
  have hnext : (Real.sqrt (orthogonalPolynomialNorm L n))⁻¹ =
      Real.sqrt (orthogonalRecurrenceBeta L (n + 1)) *
        (Real.sqrt (orthogonalPolynomialNorm L (n + 1)))⁻¹ := by
    rw [orthogonalRecurrenceBeta, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel,
      Real.sqrt_div (hH (n + 1) le_rfl).le]
    field_simp [hs n (by omega), hs (n + 1) le_rfl]
  have hprev : (Real.sqrt (orthogonalPolynomialNorm L n))⁻¹ * orthogonalRecurrenceBeta L n =
      Real.sqrt (orthogonalRecurrenceBeta L n) *
        (Real.sqrt (orthogonalPolynomialNorm L (n - 1)))⁻¹ := by
    by_cases hn : n = 0
    · simp [hn, orthogonalRecurrenceBeta]
    rw [orthogonalRecurrenceBeta, if_neg hn, Real.sqrt_div (hH n (by omega)).le]
    field_simp [hs n (by omega), hs (n - 1) (by omega), (hH (n - 1) (by omega)).ne']
    nlinarith [Real.sq_sqrt (hH n (by omega)).le,
      Real.sq_sqrt (hH (n - 1) (by omega)).le]
  have hrec : X * monicOrthogonalPolynomial L n = monicOrthogonalPolynomial L (n + 1) +
      C (orthogonalRecurrenceAlpha L n) * monicOrthogonalPolynomial L n +
      C (orthogonalRecurrenceBeta L n) * monicOrthogonalPolynomial L (n - 1) := by
    linear_combination -(monicOrthogonalPolynomial_succ_eq L n hL)
  calc
    _ = C (Real.sqrt (orthogonalPolynomialNorm L n))⁻¹ *
        (X * monicOrthogonalPolynomial L n) := by simp only [orthonormalMomentPolynomial]; ring
    _ = C (Real.sqrt (orthogonalPolynomialNorm L n))⁻¹ *
        (monicOrthogonalPolynomial L (n + 1) +
          C (orthogonalRecurrenceAlpha L n) * monicOrthogonalPolynomial L n +
          C (orthogonalRecurrenceBeta L n) * monicOrthogonalPolynomial L (n - 1)) := by rw [hrec]
    _ = _ := by
      simp only [orthonormalMomentPolynomial]
      have hcnext := congrArg (C : ℝ →+* ℝ[X]) hnext
      have hcprev := congrArg (C : ℝ →+* ℝ[X]) hprev
      simp only [map_mul] at hcnext hcprev
      linear_combination monicOrthogonalPolynomial L (n + 1) * hcnext +
        monicOrthogonalPolynomial L (n - 1) * hcprev

/-- The actual compressed multiplication matrix equals the shared finite Jacobi
coefficient matrix, with canonical positive square-root off-diagonals. This is a
proved realization identity, including the empty order-zero matrix.
Source: Gautschi (2004), Theorem 1.27; operator derivations (OF8).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial) -/
theorem orthogonalPolynomialJacobiMatrix_eq_jacobiMatrix (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ)
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k) :
    orthogonalPolynomialJacobiMatrix L n =
      jacobiMatrix (orthogonalRecurrenceAlpha L) (fun i => Real.sqrt (orthogonalRecurrenceBeta L i)) n := by
  have hsym := Matrix.isHermitian_iff_isSymm.mp (isHermitian_orthogonalPolynomialJacobiMatrix L n)
  ext i j
  simp only [jacobiMatrix, Matrix.of_apply]
  split_ifs with h0 h1 h2
  · have hij : i = j := Fin.ext h0
    subst j
    exact orthogonalPolynomialJacobiMatrix_apply_self_eq_alpha L i (hH i.val i.isLt)
  · exact orthogonalPolynomialJacobiMatrix_superdiagonal_eq_sqrt_beta L hL hH i j h1
  · rw [hsym.apply]
    exact orthogonalPolynomialJacobiMatrix_superdiagonal_eq_sqrt_beta L hL hH j i h2
  · rcases (show i.val + 1 < j.val ∨ j.val + 1 < i.val by omega) with hij | hji
    · exact orthogonalPolynomialJacobiMatrix_apply_eq_zero L hL i j hij
    · rw [hsym.apply]
      exact orthogonalPolynomialJacobiMatrix_apply_eq_zero L hL j i hji

end NLAlib
