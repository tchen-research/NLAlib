import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# Coefficient certificates for positive polynomial tails

A three-term recurrence is certified coefficientwise after a finite shift.
This is a purely algebraic alternative to locating all roots of the recurrence.
-/

noncomputable section
open Polynomial
namespace Polynomial

/-- Nonnegative coefficients give a nonnegative value on the positive half-line. -/
theorem eval_nonneg_of_coeff_nonneg {p : ℝ[X]} (hp : ∀ k, 0 ≤ p.coeff k)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ p.eval x := by
  rw [eval_eq_sum_range]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hp k) (pow_nonneg hx k)

/-- A strictly positive constant coefficient strengthens the coefficient
certificate to strict positivity, including at zero. -/
theorem eval_pos_of_coeff_nonneg_of_coeff_zero_pos {p : ℝ[X]}
    (hp : ∀ k, 0 ≤ p.coeff k) (hp0 : 0 < p.coeff 0) {x : ℝ} (hx : 0 ≤ x) :
    0 < p.eval x := by
  rw [eval_eq_sum_range]
  have h := Finset.single_le_sum
    (s := Finset.range (p.natDegree+1)) (f := fun k => p.coeff k * x^k)
    (fun k _ => mul_nonneg (hp k) (pow_nonneg hx k))
    (show 0 ∈ Finset.range (p.natDegree+1) by simp)
  simp only [pow_zero, mul_one] at h
  exact hp0.trans_le h

/-- Nonnegative coefficients are preserved by every ordinary derivative. -/
theorem coeff_iterate_derivative_nonneg {p : ℝ[X]} (hp : ∀ k, 0 ≤ p.coeff k)
    (r k : ℕ) : 0 ≤ ((derivative : ℝ[X] → ℝ[X])^[r] p).coeff k := by
  rw [coeff_iterate_derivative, nsmul_eq_mul]
  exact mul_nonneg (by positivity) (hp _)

/-- Ordinary derivatives commute with a translation of the variable. -/
theorem iterate_derivative_comp_X_add_C (p : ℝ[X]) (a : ℝ) (r : ℕ) :
    (derivative : ℝ[X] → ℝ[X])^[r] (p.comp (X+C a)) =
      ((derivative : ℝ[X] → ℝ[X])^[r] p).comp (X+C a) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, derivative_comp]
    simp only [derivative_add, derivative_X, derivative_C, add_zero, one_mul,
      Function.iterate_succ_apply']

/-- A coefficient certificate after translation gives nonnegative derivatives
throughout the entire tail, with no root-splitting assumption. -/
theorem iterate_derivative_eval_nonneg_of_shifted_coeff_nonneg
    {p : ℝ[X]} {a : ℝ} (hp : ∀ k, 0 ≤ (p.comp (X+C a)).coeff k)
    {x : ℝ} (hx : a ≤ x) (r : ℕ) :
    0 ≤ ((derivative : ℝ[X] → ℝ[X])^[r] p).eval x := by
  have h := eval_nonneg_of_coeff_nonneg (fun k => coeff_iterate_derivative_nonneg hp r k)
    (show 0 ≤ x-a by linarith)
  rw [iterate_derivative_comp_X_add_C, eval_comp, eval_add, eval_X, eval_C,
    sub_add_cancel] at h
  exact h

/-- A positive constant term in the translated coefficient certificate proves
strict positivity throughout the tail. -/
theorem eval_pos_of_shifted_coeff_nonneg {p : ℝ[X]} {a : ℝ}
    (hp : ∀ k, 0 ≤ (p.comp (X+C a)).coeff k)
    (hp0 : 0 < (p.comp (X+C a)).coeff 0) {x : ℝ} (hx : a ≤ x) :
    0 < p.eval x := by
  have h := eval_pos_of_coeff_nonneg_of_coeff_zero_pos hp hp0
    (show 0 ≤ x-a by linarith)
  simpa only [eval_comp, eval_add, eval_X, eval_C, sub_add_cancel] using h

/-- A positive linear term in the translated coefficient certificate proves
strict positivity of the derivative throughout the tail. -/
theorem derivative_eval_pos_of_shifted_coeff_nonneg {p : ℝ[X]} {a : ℝ}
    (hp : ∀ k, 0 ≤ (p.comp (X+C a)).coeff k)
    (hp1 : 0 < (p.comp (X+C a)).coeff 1) {x : ℝ} (hx : a ≤ x) :
    0 < p.derivative.eval x := by
  have hcoeff (k : ℕ) : 0 ≤ ((p.comp (X+C a)).derivative).coeff k := by
    rw [coeff_derivative]
    exact mul_nonneg (hp _) (by positivity)
  have hzero : 0 < ((p.comp (X+C a)).derivative).coeff 0 := by
    simpa only [coeff_derivative, zero_add, Nat.cast_zero, zero_add, mul_one] using hp1
  have h := eval_pos_of_coeff_nonneg_of_coeff_zero_pos hcoeff hzero
    (show 0 ≤ x-a by linarith)
  have hd := iterate_derivative_comp_X_add_C p a 1
  simp only [Function.iterate_one] at hd
  rw [hd, eval_comp, eval_add, eval_X, eval_C, sub_add_cancel] at h
  exact h

/-- Shifted monic Laguerre recurrence polynomials have nonnegative coefficients
and strictly positive constant and linear coefficients beyond `4N`.
The invariant `Q_j - j Q_(j-1)` has nonnegative coefficients. -/
theorem shifted_laguerre_recurrence_coeff_certificate
    (P : ℕ → ℝ[X]) (hP0 : P 0 = 1)
    (hP : ∀ j, P (j+1) = (X-C (2*(j:ℝ)+1)) * P j - C ((j:ℝ)^2) * P (j-1))
    (N j : ℕ) (hj : j ≤ N) :
    (∀ k, 0 ≤ ((P j).comp (X+C (4*(N:ℝ)))).coeff k) ∧
    (∀ k, 0 ≤ (((P j).comp (X+C (4*(N:ℝ)))) -
      C (j:ℝ) * ((P (j-1)).comp (X+C (4*(N:ℝ))))).coeff k) ∧
    0 < ((P j).comp (X+C (4*(N:ℝ)))).coeff 0 ∧
    (0 < j → 0 < ((P j).comp (X+C (4*(N:ℝ)))).coeff 1) := by
  let Q : ℕ → ℝ[X] := fun j => (P j).comp (X+C (4*(N:ℝ)))
  change (∀ k, 0 ≤ (Q j).coeff k) ∧
    (∀ k, 0 ≤ (Q j - C (j:ℝ)*Q (j-1)).coeff k) ∧
    0 < (Q j).coeff 0 ∧ (0 < j → 0 < (Q j).coeff 1)
  induction j with
  | zero =>
    simp [Q, hP0]
    intro k
    rw [← C_1, coeff_C]
    split_ifs <;> norm_num
  | succ j ih =>
    obtain ⟨hQ, hgap, hQ0, _⟩ := ih (by omega)
    have hrec : Q (j+1) - C ((j+1:ℕ):ℝ) * Q j =
        X*Q j + C (4*(N:ℝ)-4*j-2)*Q j + C (j:ℝ)*(Q j-C (j:ℝ)*Q (j-1)) := by
      dsimp [Q]
      rw [hP]
      apply Polynomial.funext
      intro x
      simp only [eval_comp, eval_sub, eval_mul, eval_add, eval_X, eval_C]
      push_cast
      ring
    have hscalar : 0 ≤ 4*(N:ℝ)-4*j-2 := by
      have : (j:ℝ)+1 ≤ N := by exact_mod_cast hj
      linarith
    have hX (k : ℕ) : 0 ≤ (X*Q j).coeff k := by
      cases k with
      | zero => simp
      | succ k => simpa only [coeff_X_mul] using hQ k
    have hg (k : ℕ) : 0 ≤ (Q (j+1)-C ((j+1:ℕ):ℝ)*Q j).coeff k := by
      rw [hrec, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul]
      exact add_nonneg (add_nonneg (hX k) (mul_nonneg hscalar (hQ k)))
        (mul_nonneg (by positivity) (hgap k))
    have hnext (k : ℕ) : 0 ≤ (Q (j+1)).coeff k := by
      have := hg k
      rw [coeff_sub, coeff_C_mul] at this
      nlinarith [hQ k, show (0:ℝ) ≤ j+1 by positivity]
    refine ⟨hnext, ?_, ?_, ?_⟩
    · simpa only [Nat.add_sub_cancel] using hg
    · have := hg 0
      rw [coeff_sub, coeff_C_mul] at this
      have hp : 0 < ((j+1:ℕ):ℝ) * (Q j).coeff 0 := mul_pos (by positivity) hQ0
      linarith
    · intro _
      have h1 : (Q j).coeff 0 ≤
          (Q (j+1)-C ((j+1:ℕ):ℝ)*Q j).coeff 1 := by
        rw [hrec, coeff_add, coeff_add, coeff_X_mul, coeff_C_mul, coeff_C_mul]
        have := mul_nonneg hscalar (hQ 1)
        have := mul_nonneg (show (0:ℝ) ≤ j by positivity) (hgap 1)
        linarith
      rw [coeff_sub, coeff_C_mul] at h1
      have := mul_nonneg (show (0:ℝ) ≤ j+1 by positivity) (hQ 1)
      push_cast at h1
      linarith

end Polynomial
