import NLAlib.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.LinearAlgebra.Lagrange

/-!
# Aliasing on the canonical Chebyshev extrema grid

Reduce each frequency modulo `2N`, then reflect into `[0,N]`. On the grid
`cos(jπ/N)` the resulting polynomial has the same nodal values and sup norm at most one.
This is the finite polynomial ingredient of the analytic interpolant factor-four bound.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real Set

namespace NLAlib

/-- Frequency folding into the degree range of the canonical Chebyshev extrema grid.
Source: Trefethen, ATAP, Theorem 4.1 (`chebyshev-approx-analytic`, helper). -/
def chebyshevAliasIndex (N k : ℕ) : ℕ := min (k % (2 * N)) (2 * N - k % (2 * N))

/-- Every folded frequency has degree at most the grid cutoff.
Source: Trefethen, ATAP, Theorem 4.1 (`chebyshev-approx-analytic`, helper). -/
theorem chebyshevAliasIndex_le {N : ℕ} (hN : 0 < N) (k : ℕ) : chebyshevAliasIndex N k ≤ N := by
  have hmod := Nat.mod_lt k (show 0 < 2 * N by omega)
  unfold chebyshevAliasIndex
  omega

/-- The high-frequency and folded Chebyshev polynomials have equal values at every
canonical extrema node.
Source: Trefethen, ATAP, Theorem 4.1 (`chebyshev-approx-analytic`, helper). -/
theorem eval_T_node_eq_eval_T_alias {N : ℕ} (hN : 0 < N) (k j : ℕ) :
    (T ℝ (k : ℤ)).eval (node N j) =
      (T ℝ (chebyshevAliasIndex N k : ℤ)).eval (node N j) := by
  rw [node, T_real_cos, T_real_cos]
  norm_cast
  let v := k % (2 * N)
  let m := k / (2 * N)
  have hk : k = v + 2 * N * m := by
    dsimp [v, m]
    exact (Nat.mod_add_div k (2 * N)).symm
  have hmod : v < 2 * N := Nat.mod_lt k (by omega)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hangle : (k : ℝ) * (j * Real.pi / N) = (v : ℝ) * (j * Real.pi / N) +
      (m * j : ℕ) * (2 * Real.pi) := by
    rw [hk]
    push_cast
    field_simp
  rw [hangle, cos_add_nat_mul_two_pi]
  rcases le_or_gt v N with hv | hv
  · have hidx : chebyshevAliasIndex N k = v := by unfold chebyshevAliasIndex; dsimp [v] at hv ⊢; omega
    rw [hidx]
  · have hidx : chebyshevAliasIndex N k = 2 * N - v := by
      unfold chebyshevAliasIndex
      change min v (2 * N - v) = 2 * N - v
      omega
    rw [hidx]
    have hangle' : (v : ℝ) * (j * Real.pi / N) =
        (j : ℝ) * (2 * Real.pi) - ((2 * N - v : ℕ) : ℝ) * (j * Real.pi / N) := by
      rw [Nat.cast_sub hmod.le]
      push_cast
      field_simp
      ring
    rw [hangle', cos_nat_mul_two_pi_sub]

/-- Canonical Chebyshev grid nodes are injective on their index range.
Source: Mathlib `strictAntiOn_node`; helper for `chebyshev-approx-analytic`. -/
theorem chebyshev_node_injOn (N : ℕ) : Set.InjOn (node N) (Finset.range (N + 1) : Set ℕ) :=
  (strictAntiOn_node N).injOn

/-- Interpolating a high Chebyshev frequency on the canonical extrema grid gives precisely
its folded Chebyshev polynomial.
Source: Trefethen, ATAP, Theorem 4.1 (`chebyshev-approx-analytic`, helper). -/
theorem interpolate_eval_T_node_eq_T_alias {N : ℕ} (hN : 0 < N) (k : ℕ) :
    Lagrange.interpolate (range (N + 1)) (node N)
      (fun j => (T ℝ (k : ℤ)).eval (node N j)) = T ℝ (chebyshevAliasIndex N k : ℤ) := by
  symm
  refine Lagrange.eq_interpolate_of_eval_eq _ (chebyshev_node_injOn N) ?_ ?_
  · rw [degree_T, Int.natAbs_natCast, card_range]
    exact_mod_cast (Nat.lt_succ_of_le (chebyshevAliasIndex_le hN k))
  · intro j hj
    exact (eval_T_node_eq_eval_T_alias hN k j).symm

/-- Every interpolated Chebyshev frequency remains bounded by one on `[-1,1]`.
Source: Trefethen, ATAP, Theorem 4.1 (`chebyshev-approx-analytic`, helper). -/
theorem abs_eval_interpolate_eval_T_node_le_one {N : ℕ} (hN : 0 < N) (k : ℕ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(Lagrange.interpolate (range (N + 1)) (node N)
      (fun j => (T ℝ (k : ℤ)).eval (node N j))).eval x| ≤ 1 := by
  rw [interpolate_eval_T_node_eq_T_alias hN]
  exact abs_eval_T_real_le_one _ (abs_le.mpr hx)

end NLAlib
