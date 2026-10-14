import NLAlib.Krylov.Quadrature.Jacobi

/-! # The confluent kernel of actual signed Lanczos polynomials

Formal differentiation of the multiplied Christoffel–Darboux polynomial identity
gives the diagonal Wronskian. The square sum is strictly positive from its nonzero
constant polynomial, independently of orientation of the actual basis.
-/

noncomputable section
open Polynomial Matrix MeasureTheory Finset
open scoped Matrix

namespace NLAlib.LanczosDecomp

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- The actual signed Lanczos polynomials have a strictly positive confluent
Christoffel–Darboux kernel in every normalized positive-order range. At the terminal
order use the monic norm-divided formula instead of a nonexistent normalized polynomial.
Source: Gautschi (2004), Corollary to Theorem 1.32; operator derivations (OF11).
atlas: monic-orthogonal-recurrence (partial), jacobi-matrix-identities (partial) -/
theorem sum_sq_eval_poly_eq_confluent_and_pos (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    {m : ℕ} (hm0 : 0 < m) (hm : m < q) (x : ℝ) :
    (∑ j ∈ range m, (D.poly j).eval x ^ 2) =
      D.beta m * ((D.poly m).derivative.eval x * (D.poly (m - 1)).eval x -
        (D.poly (m - 1)).derivative.eval x * (D.poly m).eval x) ∧
      0 < ∑ j ∈ range m, (D.poly j).eval x ^ 2 := by
  let K : ℝ[X] := ∑ j ∈ range m, C ((D.poly j).eval x) * D.poly j
  have hpol : (X - C x) * K = C (D.beta m) *
      (C ((D.poly (m - 1)).eval x) * D.poly m -
        C ((D.poly m).eval x) * D.poly (m - 1)) := by
    apply Polynomial.funext
    intro y
    have he := D.sub_mul_sum_eval_poly_mul hA hm0 hm y x
    simp only [K, eval_mul, eval_sub, eval_X, eval_C, eval_finsetSum]
    convert he using 1
    · congr 1
      exact sum_congr rfl fun j _ => mul_comm _ _
    · ring
  have hd := congrArg (fun p : ℝ[X] => p.derivative.eval x) hpol
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    zero_mul, one_mul, zero_add, eval_add, eval_mul, eval_sub, eval_X, eval_C,
    sub_self, zero_mul, add_zero] at hd
  have hK : K.eval x = ∑ j ∈ range m, (D.poly j).eval x ^ 2 := by
    simp only [K, eval_finsetSum, eval_mul, eval_C, pow_two]
  refine ⟨?_, ?_⟩
  · rw [← hK, hd]
    ring
  · apply sum_pos' (fun j _ => sq_nonneg _)
    refine ⟨0, mem_range.mpr hm0, ?_⟩
    have hp : (D.poly 0).natDegree = 0 :=
      natDegree_eq_of_degree_eq_some (D.degree_poly (by omega))
    have hp0 : D.poly 0 ≠ 0 := by
      intro h
      have hd0 := D.degree_poly (show 0 < q by omega)
      simp [h] at hd0
    rw [eq_C_of_natDegree_eq_zero hp, eval_C]
    exact sq_pos_of_ne_zero (fun hc => hp0 (by rw [eq_C_of_natDegree_eq_zero hp, hc, C_0]))

end NLAlib.LanczosDecomp
