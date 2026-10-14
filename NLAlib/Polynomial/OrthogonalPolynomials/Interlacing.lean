import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMatrix
import NLAlib.Matrix.Spectral.CourantFischer

/-! # No common zeros and strict Jacobi interlacing

The three-term recurrence propagates a common zero down to the constant
polynomial. Cauchy interlacing together with this obstruction makes the
interlacing inequalities strict for positive finite moment systems.
Source: Gautschi (2004), Theorem 1.19; operator derivations OP8–OP11.
-/

noncomputable section

open Polynomial Matrix
open scoped Matrix

namespace NLAlib

/-- Consecutive monic orthogonal polynomials have no common zero whenever the
moment systems through the larger order are nonsingular. This holds over any field.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem not_eval_monicOrthogonalPolynomial_eq_zero_and_succ
    {𝕜 : Type*} [Field 𝕜] (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ)
    (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0) (x : 𝕜) :
    ¬ ((monicOrthogonalPolynomial L n).eval x = 0 ∧
      (monicOrthogonalPolynomial L (n + 1)).eval x = 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rintro ⟨h1, h2⟩
    have hnorm1 : orthogonalPolynomialNorm L (n + 1) ≠ 0 :=
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L
        (hL (n + 1) (by omega))).functional_sq_ne_zero (hL (n + 1 + 1) le_rfl)
    have hnorm0 : orthogonalPolynomialNorm L n ≠ 0 :=
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L
        (hL n (by omega))).functional_sq_ne_zero (hL (n + 1) (by omega))
    have hb : orthogonalRecurrenceBeta L (n + 1) ≠ 0 := by
      rw [orthogonalRecurrenceBeta, if_neg (by omega), Nat.add_sub_cancel]
      exact div_ne_zero hnorm1 hnorm0
    have hrec := congrArg (eval x) (monicOrthogonalPolynomial_succ_eq L (n + 1) hL)
    simp only [eval_sub, eval_mul, eval_X, eval_C, Nat.add_sub_cancel] at hrec
    rw [h1, h2, mul_zero, zero_sub] at hrec
    have h0 : (monicOrthogonalPolynomial L n).eval x = 0 := by
      exact (mul_eq_zero.mp (neg_eq_zero.mp hrec.symm)).resolve_left hb
    exact ih (fun k hk => hL k (by omega)) ⟨h0, h1⟩

private theorem eval_monicOrthogonalPolynomial_eigenvalues₀_eq_zero
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k)
    (i : Fin (Fintype.card (Fin n))) :
    (monicOrthogonalPolynomial L n).eval
      ((isHermitian_orthogonalPolynomialJacobiMatrix L n).eigenvalues₀ i) = 0 := by
  let hB := isHermitian_orthogonalPolynomialJacobiMatrix L n
  have hmem : hB.eigenvalues₀ i ∈ Set.range hB.eigenvalues := by
    rw [← hB.range_eigenvalues₀]
    exact ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := hmem
  rw [← hj]
  exact eval_monicOrthogonalPolynomial_eigenvalues_eq_zero L hL hH j

/-- Eigenvalues of consecutive moment Jacobi matrices strictly interlace.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eigenvalues₀_orthogonalPolynomialJacobiMatrix_strict_interlacing
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n + 1, 0 < orthogonalPolynomialNorm L k) (i : Fin n) :
    (isHermitian_orthogonalPolynomialJacobiMatrix L (n + 1)).eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + 1)).symm i.succ) <
      (isHermitian_orthogonalPolynomialJacobiMatrix L n).eigenvalues₀
        (Fin.cast (Fintype.card_fin n).symm i) ∧
      (isHermitian_orthogonalPolynomialJacobiMatrix L n).eigenvalues₀
        (Fin.cast (Fintype.card_fin n).symm i) <
      (isHermitian_orthogonalPolynomialJacobiMatrix L (n + 1)).eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + 1)).symm i.castSucc) := by
  let hB := isHermitian_orthogonalPolynomialJacobiMatrix L n
  let hC := isHermitian_orthogonalPolynomialJacobiMatrix L (n + 1)
  let e : Fin n ↪ Fin (n + 1) := ⟨Fin.castSucc, Fin.castSucc_injective n⟩
  let k : Fin (Fintype.card (Fin n)) := Fin.cast (Fintype.card_fin n).symm i
  have hup := hC.eigenvalues₀_submatrix_le e k
  have hlo := hC.eigenvalues₀_le_eigenvalues₀_submatrix e k
  have hsub : (orthogonalPolynomialJacobiMatrix L (n + 1)).submatrix e e =
      orthogonalPolynomialJacobiMatrix L n := by rfl
  rw [(hC.submatrix e).eigenvalues₀_congr hB hsub k] at hup hlo
  have hup' : hB.eigenvalues₀ k ≤ hC.eigenvalues₀
      (Fin.cast (Fintype.card_fin (n + 1)).symm i.castSucc) := by
    convert hup using 1
    congr 1
  have hlo' : hC.eigenvalues₀ (Fin.cast (Fintype.card_fin (n + 1)).symm i.succ) ≤
      hB.eigenvalues₀ k := by
    convert hlo using 1
    congr 1
    apply Fin.ext
    simp only [k, Fin.val_cast, Fin.val_succ, Fintype.card_fin]
    omega
  have hroot := eval_monicOrthogonalPolynomial_eigenvalues₀_eq_zero L
    (fun j hj => hL j (by omega)) (fun j hj => hH j (by omega)) k
  have hne (j : Fin (Fintype.card (Fin (n + 1)))) : hC.eigenvalues₀ j ≠ hB.eigenvalues₀ k := by
    intro heq
    have hnext := eval_monicOrthogonalPolynomial_eigenvalues₀_eq_zero L hL hH j
    rw [heq] at hnext
    exact not_eval_monicOrthogonalPolynomial_eq_zero_and_succ L n hL _ ⟨hroot, hnext⟩
  exact ⟨lt_of_le_of_ne hlo' (hne _), lt_of_le_of_ne hup' (hne _).symm⟩

end NLAlib
