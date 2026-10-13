import NLAlib.Polynomial.BestApproximation.Basic
import NLAlib.ForMathlib.Algebra.OrderedNodalWeights
import Mathlib.Tactic.Ring

/-!
# Signs of barycentric coefficients for interval peaks

The gap-sign polynomial has positive barycentric coefficients to the left of its gap and
negative ones to the right, up to one common sign.
Source: the finite nodal Wronskian sum-of-squares route.
-/

noncomputable section

open Finset

namespace NLAlib

/-- Multiplying a gap cardinal sign by its ordered nodal weight leaves a common sign and
an absolute weight, with the expected sign reversal across the gap.
Source: the alternating sign of ordered Lagrange nodal weights. -/
theorem interpolationGapSign_mul_nodalWeight {n : ℕ} {v : Fin (n + 2) → ℝ}
    (hv : StrictMono v) (i : Fin (n + 1)) (k : Fin (n + 2)) :
    interpolationGapSign n i k * Lagrange.nodalWeight univ v k =
      (-1 : ℝ) ^ (i.val + n + 1) *
        (if k.val ≤ i.val then |Lagrange.nodalWeight univ v k|
          else -|Lagrange.nodalWeight univ v k|) := by
  have hpos := signed_nodalWeight_pos (n := n + 1) hv k
  have habs : |Lagrange.nodalWeight univ v k| =
      (-1 : ℝ) ^ (n + 1 - k.val) * Lagrange.nodalWeight univ v k := by
    simpa only [abs_mul, abs_neg_one_pow, one_mul] using abs_of_pos hpos
  rw [habs]
  unfold interpolationGapSign
  split_ifs with hki
  · have he : i.val + n + 1 = (i.val - k.val) + (n + 1 - k.val) + 2 * k.val := by omega
    rw [he, pow_add, pow_add, pow_mul]
    have hp : (-1 : ℝ) ^ 2 = 1 := by norm_num
    rw [hp, one_pow, mul_one]
    have hs : ((-1 : ℝ) ^ (n + 1 - k.val)) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    calc
      _ = (-1 : ℝ) ^ (i.val - k.val) * (((-1 : ℝ) ^ (n + 1 - k.val)) ^ 2 * Lagrange.nodalWeight univ v k) := by rw [hs, one_mul]
      _ = _ := by ring
  · have he : i.val + n + 1 = (k.val - i.val - 1) + (n + 1 - k.val) + (2 * i.val + 1) := by omega
    rw [he, pow_add, pow_add, pow_add, pow_mul]
    have hp : (-1 : ℝ) ^ 2 = 1 := by norm_num
    rw [hp, one_pow, one_mul, pow_one]
    have hs : ((-1 : ℝ) ^ (n + 1 - k.val)) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    calc
      _ = (-1 : ℝ) ^ (k.val - i.val - 1) * (((-1 : ℝ) ^ (n + 1 - k.val)) ^ 2 * Lagrange.nodalWeight univ v k) := by rw [hs, one_mul]
      _ = _ := by ring



/-- Two gap sign vectors agree up to one common sign outside the intervening nodes,
and have the opposite sign on the intervening nodes.
Source: the finite nodal decomposition of the gap-polynomial pair. -/
theorem interpolationGapSign_relative {n : ℕ} {v : Fin (n + 2) → ℝ}
    (hv : StrictMono v) (i j : Fin (n + 1)) (hij : i ≤ j) (k : Fin (n + 2)) :
    (-1 : ℝ) ^ (j.val - i.val) * interpolationGapSign n j k =
      if i.val < k.val ∧ k.val ≤ j.val then -interpolationGapSign n i k
        else interpolationGapSign n i k := by
  have hw : Lagrange.nodalWeight univ v k ≠ 0 := Lagrange.nodalWeight_ne_zero hv.injective.injOn (mem_univ k)
  apply mul_right_cancel₀ hw
  let s : ℝ := (-1 : ℝ) ^ (j.val - i.val)
  have hs : s ^ 2 = 1 := by dsimp [s]; rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have he : j.val + n + 1 = (i.val + n + 1) + (j.val - i.val) := by have := hij; omega
  have hcommon : s * (-1 : ℝ) ^ (j.val + n + 1) = (-1 : ℝ) ^ (i.val + n + 1) := by
    rw [he, pow_add]
    change s * ((-1 : ℝ) ^ (i.val + n + 1) * s) = _
    calc
      _ = (-1 : ℝ) ^ (i.val + n + 1) * s ^ 2 := by ring
      _ = _ := by rw [hs, mul_one]
  rw [mul_assoc, interpolationGapSign_mul_nodalWeight hv j k, ← mul_assoc, hcommon]
  by_cases hki : k.val ≤ i.val
  · have hkj : k.val ≤ j.val := by have := hij; omega
    rw [if_pos hkj, if_neg (by omega), interpolationGapSign_mul_nodalWeight hv i k, if_pos hki]
  · by_cases hkj : k.val ≤ j.val
    · rw [if_pos hkj, if_pos (by omega), neg_mul, interpolationGapSign_mul_nodalWeight hv i k, if_neg hki]
      ring
    · rw [if_neg hkj, if_neg (by omega), interpolationGapSign_mul_nodalWeight hv i k, if_neg hki]

end NLAlib
