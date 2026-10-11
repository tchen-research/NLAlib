import NLAlib.Polynomial.SawtoothZeros
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Alternating sign of the actual sawtooth interpolation error

The exhausted root count gives a root-free grid cell. The intermediate value theorem
propagates a sign throughout a cell, and Fermat excludes equal signs on adjacent cells
because the interpolation zero has a genuinely nonzero derivative.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real Set Filter
open scoped Topology

namespace NLAlib

/-- The sawtooth error is nonzero strictly inside every half-period grid cell.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothError_ne_zero_of_between_grid {n j : ℕ} (hj : j ≤ n) {t : ℝ}
    (ht : t ∈ Ioo (sawtoothGridAngle n j) (sawtoothGridAngle n (j + 1))) :
    sawtoothError n t ≠ 0 := by
  intro hzero
  have hleft := sawtoothGridAngle_mem_Icc (n := n) (j := j) (by omega)
  have hright := sawtoothGridAngle_mem_Icc (n := n) (j := j + 1) (by omega)
  have hg := mem_sawtoothZeroGrid_of_sawtoothError_eq_zero
    ⟨hleft.1.trans ht.1.le, ht.2.le.trans hright.2⟩ hzero
  obtain ⟨k, hk, hkt⟩ := Finset.mem_image.mp hg
  rw [← hkt] at ht
  have h1 := (strictMono_sawtoothGridAngle n).lt_iff_lt.mp ht.1
  have h2 := (strictMono_sawtoothGridAngle n).lt_iff_lt.mp ht.2
  omega

/-- A scaled sawtooth error with positive value at one point has positive value throughout
the same root-free cell. This is the actual intermediate-value argument, not a sign premise.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem mul_sawtoothError_pos_of_pos_on_cell {n j : ℕ} (hj : j ≤ n) {s x y : ℝ}
    (hs : s ≠ 0) (hx : x ∈ Ioo (sawtoothGridAngle n j) (sawtoothGridAngle n (j + 1)))
    (hy : y ∈ Ioo (sawtoothGridAngle n j) (sawtoothGridAngle n (j + 1)))
    (hpos : 0 < s * sawtoothError n x) : 0 < s * sawtoothError n y := by
  by_contra hnot
  have hn : s * sawtoothError n y ≤ 0 := le_of_not_gt hnot
  have hc : Continuous (fun t => s * sawtoothError n t) :=
    continuous_const.mul (continuous_sawtoothError n)
  obtain ⟨z, hz, hzero⟩ := isPreconnected_Ioo.intermediate_value hy hx hc.continuousOn ⟨hn, hpos.le⟩
  exact mul_ne_zero hs (sawtoothError_ne_zero_of_between_grid hj hz) hzero

/-- The actual sawtooth error is positive in the first half-period grid cell, because
its origin value is pi and there are no extra zeros.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothError_pos_on_first_cell (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (sawtoothGridAngle n 0) (sawtoothGridAngle n 1)) : 0 < sawtoothError n t := by
  have ht0 : 0 < t := by simpa [sawtoothGridAngle] using ht.1
  by_contra hnot
  have hn : sawtoothError n t ≤ 0 := le_of_not_gt hnot
  have h0 : sawtoothError n 0 = Real.pi := by simp [sawtoothError]
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' ht0.le (continuous_sawtoothError n).continuousOn
    (show (0 : ℝ) ∈ Icc (sawtoothError n t) (sawtoothError n 0) by rw [h0]; exact ⟨hn, Real.pi_pos.le⟩)
  have hzpos : 0 < z := by
    rcases eq_or_lt_of_le hz.1 with hzeq | hzeq
    · rw [← hzeq, h0] at hzero
      exact (Real.pi_ne_zero hzero).elim
    · exact hzeq
  have hcell : z ∈ Ioo (sawtoothGridAngle n 0) (sawtoothGridAngle n 1) :=
    ⟨by simpa [sawtoothGridAngle] using hzpos, hz.2.trans_lt ht.2⟩
  exact sawtoothError_ne_zero_of_between_grid (Nat.zero_le n) hcell hzero

/-- The actual sawtooth-error sign alternates on successive grid cells: the scaled error
`(-1)^j(B-τ_n)` is strictly positive. A failed sign flip would give a local extremum at a
simple interpolation zero, contradicting Fermat's theorem.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem mul_sawtoothError_pos_on_grid_cell (n j : ℕ) (hj : j ≤ n) {t : ℝ}
    (ht : t ∈ Ioo (sawtoothGridAngle n j) (sawtoothGridAngle n (j + 1))) :
    0 < (-1 : ℝ) ^ j * sawtoothError n t := by
  have hall : ∀ j : ℕ, j ≤ n → ∀ t ∈ Ioo (sawtoothGridAngle n j) (sawtoothGridAngle n (j + 1)),
      0 < (-1 : ℝ) ^ j * sawtoothError n t := by
    intro j
    induction j with
    | zero =>
      intro hj t ht
      simpa only [pow_zero, one_mul] using sawtoothError_pos_on_first_cell n ht
    | succ j ih =>
      intro hj t ht
      by_contra hnot
      let s := (-1 : ℝ) ^ j
      have hs : s ≠ 0 := pow_ne_zero _ (by norm_num)
      have hsame : 0 < s * sawtoothError n t := by
        have hnn : s * sawtoothError n t ≠ 0 := mul_ne_zero hs (sawtoothError_ne_zero_of_between_grid hj ht)
        have hle := le_of_not_gt hnot
        rw [pow_succ] at hle
        have hge : 0 ≤ s * sawtoothError n t := by dsimp [s]; nlinarith
        exact lt_of_le_of_ne hge (Ne.symm hnn)
      have hnew : ∀ y ∈ Ioo (sawtoothGridAngle n (j + 1)) (sawtoothGridAngle n (j + 2)),
          0 < s * sawtoothError n y :=
        fun y hy => mul_sawtoothError_pos_of_pos_on_cell hj hs ht hy hsame
      have hnode : sawtoothError n (sawtoothGridAngle n (j + 1)) = 0 :=
        sawtoothError_grid_eq_zero (by omega) (by omega)
      have hlocal : IsLocalMin (fun y => s * sawtoothError n y) (sawtoothGridAngle n (j + 1)) := by
        change ∀ᶠ y in 𝓝 (sawtoothGridAngle n (j + 1)),
          s * sawtoothError n (sawtoothGridAngle n (j + 1)) ≤ s * sawtoothError n y
        refine Filter.mem_of_superset (Ioo_mem_nhds
          (strictMono_sawtoothGridAngle n (show j < j + 1 by omega))
          (strictMono_sawtoothGridAngle n (show j + 1 < j + 2 by omega))) ?_
        intro y hy
        rw [hnode, mul_zero]
        rcases lt_trichotomy y (sawtoothGridAngle n (j + 1)) with hleft | rfl | hright
        · exact (ih (by omega) y ⟨hy.1, hleft⟩).le
        · simp [hnode]
        · exact (hnew y ⟨hright, hy.2⟩).le
      have hder := (hasDerivAt_sawtoothError n (sawtoothGridAngle n (j + 1))).const_mul s
      have hzero := hlocal.hasDerivAt_eq_zero hder
      exact mul_ne_zero hs (neg_ne_zero.mpr (eval_sawtoothErrorDerivativePolynomial_grid_ne_zero (by omega))) hzero
  exact hall j hj t ht

/-- The absolute interpolation error equals its alternating signed value on each cell.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem abs_sawtoothError_eq_mul_on_grid_cell (n j : ℕ) (hj : j ≤ n) {t : ℝ}
    (ht : t ∈ Ioo (sawtoothGridAngle n j) (sawtoothGridAngle n (j + 1))) :
    |sawtoothError n t| = (-1 : ℝ) ^ j * sawtoothError n t := by
  have h := abs_of_pos (mul_sawtoothError_pos_on_grid_cell n j hj ht)
  rw [abs_mul, abs_neg_one_pow, one_mul] at h
  exact h

/-- The odd sine interpolant has the required full-period reflection symmetry.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothApprox_two_pi_sub (n : ℕ) (t : ℝ) :
    sawtoothApprox n (2 * Real.pi - t) = -sawtoothApprox n t := by
  simp [sawtoothApprox, sin_two_pi_sub, cos_two_pi_sub]

/-- The unwrapped sawtooth error changes sign under reflection about pi.
Source: operator rederivations `rt:sawtooth` (`jackson-lipschitz`, helper). -/
theorem sawtoothError_two_pi_sub (n : ℕ) (t : ℝ) :
    sawtoothError n (2 * Real.pi - t) = -sawtoothError n t := by
  unfold sawtoothError
  rw [sawtoothApprox_two_pi_sub]
  ring

end NLAlib
