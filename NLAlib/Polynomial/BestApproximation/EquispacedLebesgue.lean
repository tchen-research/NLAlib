import NLAlib.Polynomial.BestApproximation.InterpolationProjection
import NLAlib.ForMathlib.LinearAlgebra.LagrangeAffine
import NLAlib.ForMathlib.LinearAlgebra.LagrangeIntegerGrid

/-!
# Exponential Lebesgue growth for equispaced nodes

Affine invariance reduces the exact cardinal sum to the integer-grid binomial
formula at the first half-grid point.
Atlas: the equispaced clause of `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Set Finset Polynomial

namespace NLAlib

/-- Equispaced interpolation has the strict exponential Lebesgue lower bound.
Source: Trefethen, ATAP, Thm 15.2; operator reroutes, equispaced finite proof.
The equivalent expression `2^n/(4n²)` retains the printed negative exponent when `n=1`.
atlas: lebesgue-constant-lower-bound (partial) -/
theorem pow_two_div_four_mul_sq_lt_lebesgueConstant_equispaced {n : ℕ} (hn : 0 < n) :
    (2 : ℝ) ^ n / (4 * (n : ℝ) ^ 2) < lebesgueConstant (Icc (-1 : ℝ) 1)
      (fun j : Fin (n + 1) => -1 + 2 * (j : ℝ) / n) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hα : (2 / (n : ℝ)) ≠ 0 := div_ne_zero (by norm_num) hnreal.ne'
  have hcard (j : Fin (n + 1)) :
      |(Lagrange.basis univ (fun k : Fin (n + 1) => -1 + 2 * (k : ℝ) / n) j).eval (-1 + (1 : ℝ) / n)| =
      |(Lagrange.basis (range (n + 1)) (fun k : ℕ => (k : ℝ)) j).eval (1 / 2)| := by
    have h := eval_lagrange_basis_affine univ (fun k : Fin (n + 1) => (k : ℝ)) j
      (1 / 2) (2 / n) (-1) hα
    have hv : (fun k : Fin (n + 1) => (2 / (n : ℝ)) * (k : ℝ) + -1) =
        (fun k : Fin (n + 1) => -1 + 2 * (k : ℝ) / n) := by funext k; ring
    have hx : (2 / (n : ℝ)) * (1 / 2) + -1 = -1 + 1 / n := by ring
    rw [hv, hx, lagrange_basis_univ_fin_eq_range] at h
    exact congrArg abs h
  have hsum : lebesgueFunction (fun j : Fin (n + 1) => -1 + 2 * (j : ℝ) / n) (-1 + (1 : ℝ) / n) =
      ∑ j ∈ range (n + 1),
        |(Lagrange.basis (range (n + 1)) (fun k : ℕ => (k : ℝ)) j).eval (1 / 2)| := by
    unfold lebesgueFunction
    simp_rw [hcard]
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      |(Lagrange.basis (range (n + 1)) (fun k : ℕ => (k : ℝ)) j).eval (1 / 2)|) (n + 1)
  have hx : (-1 + 1 / (n : ℝ)) ∈ Icc (-1 : ℝ) 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    constructor
    · linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hnreal.le]
    · have hdiv : (1 : ℝ) / n ≤ 2 := (div_le_iff₀ hnreal).mpr (by linarith)
      linarith
  have h := pow_two_div_four_mul_sq_lt_sum_abs_lagrange_basis hn
  rw [← hsum] at h
  exact h.trans_le (lebesgueFunction_le_lebesgueConstant _ hx)

end NLAlib
