import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Module
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Clenshaw evaluation of finite three-term expansions

A total backward recursion and its evaluation identity for arbitrary module-valued
three-term sequences. Scalar, polynomial, and matrix-vector instances are special cases.
Atlas: `clenshaw-recurrence`.
-/

noncomputable section

open Finset

namespace NLAlib

/-- The two adjacent backward Clenshaw values for `n` coefficients starting at `k`.
Source: Gautschi, Orthogonal Polynomials (2004), Algorithms 2.2 and 2.3.
The terminal pair is `(0,0)`, so this also defines the empty expansion. -/
def clenshawState {R : Type*} [Ring R] (α β c : ℕ → R) : ℕ → ℕ → R × R
  | _, 0 => (0, 0)
  | k, n + 1 =>
      let v := clenshawState α β c (k + 1) n
      (c k + α k * v.1 - β (k + 1) * v.2, v.1)

/-- A finite sum of any module-valued three-term sequence is evaluated by the total
backward Clenshaw recursion. This includes polynomial and matrix-vector evaluation
without spectral or invertibility hypotheses.
Source: Gautschi, Orthogonal Polynomials (2004), Algorithms 2.2 and 2.3;
operator rederivations, equation `polyseries:clenshawidentity`.
atlas: clenshaw-recurrence (partial) -/
theorem sum_smul_eq_clenshawState {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (α β c : ℕ → R) (y : ℕ → M)
    (hy : ∀ k, y (k + 2) = α (k + 1) • y (k + 1) - β (k + 1) • y k)
    (k n : ℕ) :
    (∑ j ∈ range n, c (k + j) • y (k + j)) =
      (clenshawState α β c k n).1 • y k +
      (clenshawState α β c k n).2 • (y (k + 1) - α k • y k) := by
  induction n generalizing k with
  | zero => simp [clenshawState]
  | succ n ih =>
    rw [sum_range_succ']
    have hshift : (∑ j ∈ range n, c (k + (j + 1)) • y (k + (j + 1))) =
        ∑ j ∈ range n, c ((k + 1) + j) • y ((k + 1) + j) := by
      apply sum_congr rfl
      intro j hj
      congr 2 <;> omega
    rw [hshift, ih]
    simp only [Nat.add_zero, clenshawState]
    have hstep := hy k
    rw [show k + 1 + 1 = k + 2 by omega, hstep]
    module

/-- A finite Chebyshev series is evaluated by the standard `u₀ − t u₁` Clenshaw formula.
Source: Gautschi, Orthogonal Polynomials (2004), Algorithm 2.2;
operator rederivations, `polyseries:clenshaw`.
atlas: clenshaw-recurrence (partial) -/
theorem sum_mul_eval_T_eq_clenshawState {R : Type*} [CommRing R] (c : ℕ → R) (t : R) (n : ℕ) :
    (∑ j ∈ range (n + 1), c j * (Polynomial.Chebyshev.T R (j : ℤ)).eval t) =
      (clenshawState (fun _ => 2 * t) (fun _ => 1) c 0 (n + 1)).1 -
        t * (clenshawState (fun _ => 2 * t) (fun _ => 1) c 0 (n + 1)).2 := by
  have hy : ∀ k : ℕ,
      (Polynomial.Chebyshev.T R ((k + 2 : ℕ) : ℤ)).eval t =
        (2 * t) * (Polynomial.Chebyshev.T R ((k + 1 : ℕ) : ℤ)).eval t -
          (Polynomial.Chebyshev.T R (k : ℤ)).eval t := by
    intro k
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      Polynomial.Chebyshev.T_add_two]
    simp
  have h := sum_smul_eq_clenshawState (fun _ => 2 * t) (fun _ => (1 : R)) c
    (fun k => (Polynomial.Chebyshev.T R (k : ℤ)).eval t) (by simp [smul_eq_mul]) 0 (n + 1)
  simp only [Nat.zero_add, smul_eq_mul, Nat.cast_zero, Polynomial.Chebyshev.T_zero,
    Polynomial.eval_one, Nat.cast_one, Polynomial.Chebyshev.T_one, Polynomial.eval_X,
    mul_one] at h
  rw [h]
  ring

end NLAlib
