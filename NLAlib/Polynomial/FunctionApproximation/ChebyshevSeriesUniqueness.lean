import NLAlib.Polynomial.FunctionApproximation.ChebyshevSeries

/-!
# Uniqueness of absolutely convergent Chebyshev expansions

Uniform control of an absolute Chebyshev series and bounded coefficient functionals
identify its coefficients with the canonical cosine-integral coefficients.
Atlas: `chebyshev-series-convergence`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real Set Filter
open scoped Topology

namespace NLAlib

/-- An absolutely summable Chebyshev expansion of a continuous function has precisely its
canonical integral coefficients. This gives uniqueness without an assumed Fourier basis.
Source: Trefethen, ATAP, Theorem 3.1; uniform series integration expressed through the
bounded coefficient functionals.
atlas: chebyshev-series-convergence (partial) -/
theorem eq_chebyshevCoeff_of_hasSum {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {a : ℕ → ℝ}
    (hs : Summable (fun k => |a k|))
    (hseries : ∀ x ∈ Icc (-1 : ℝ) 1,
      HasSum (fun k => a k * (T ℝ (k : ℤ)).eval x) (f x)) (k : ℕ) :
    a k = chebyshevCoeff f k := by
  have hbound : ∀ j x, x ∈ Icc (-1 : ℝ) 1 →
      ‖a j * (T ℝ (j : ℤ)).eval x‖ ≤ |a j| := by
    intro j x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_eval_T_real_le_one _ (abs_le.mpr hx))
      (abs_nonneg _)).trans_eq (mul_one _)
  have hu := (tendstoUniformlyOn_tsum_nat hs hbound).congr_right
    (fun x hx => (hseries x hx).tsum_eq)
  have hshift : TendstoUniformlyOn
      (fun n x => ∑ j ∈ range (n + 1), a j * (T ℝ (j : ℤ)).eval x) f atTop
      (Icc (-1 : ℝ) 1) := fun v hv => (tendsto_add_atTop_nat 1).eventually (hu v hv)
  symm
  apply eq_of_forall_dist_le
  intro ε hε
  have hU := (Metric.tendstoUniformlyOn_iff.mp hshift) (ε / 2) (by positivity)
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp hU
  let n := m + k
  let p : ℝ[X] := ∑ j ∈ range (n + 1), a j • T ℝ (j : ℤ)
  have hp : chebyshevCoeff p.eval k = a k := by
    rw [chebyshevCoeff_eval_sum_smul_T, if_pos (by dsimp [n]; omega)]
  have hE : ∀ x ∈ Icc (-1 : ℝ) 1, |f x - p.eval x| ≤ ε / 2 := by
    intro x hx
    have h := hm n (by dsimp [n]; omega) x hx
    simpa only [p, eval_finsetSum, eval_smul, smul_eq_mul, Real.dist_eq] using h.le
  have hdiff : chebyshevCoeff (fun x => f x - p.eval x) k = chebyshevCoeff f k - a k := by
    rw [chebyshevCoeff_sub hf (by fun_prop), hp]
  rw [Real.dist_eq]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h := abs_chebyshevCoeff_zero_le hE
    rw [hdiff] at h
    linarith
  · have h := abs_chebyshevCoeff_le_two_mul hE hk
    rw [hdiff] at h
    linarith

end NLAlib
