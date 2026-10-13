import NLAlib.ForMathlib.Analysis.LobattoKernelSum
import NLAlib.Polynomial.BestApproximation.LobattoCotangent

/-!
# Sharp Lobatto cardinal-kernel bound

The cotangent-pair inequality identifies the central phase as a maximum in each grid cell.
Source: focused polynomial-approximation rederivations, Theorem `thm:lobatto`.
-/

noncomputable section

open Real Finset Set

namespace NLAlib

private theorem phase_cot_pair_le {h u α : ℝ} (hh : 0 < h) (hhπ : h ≤ π / 2)
    (hu : h / 2 ≤ u) (huπ : u ≤ π / 2) (hα : α ∈ Ioo (0 : ℝ) 1) :
    sin (π * α) * (Real.cot (u + h * (α - 1 / 2)) +
      Real.cot (u - h * (α - 1 / 2))) ≤ 2 * Real.cot u := by
  rcases le_or_gt (1 / 2 : ℝ) α with ha | ha
  · have hs : α - 1 / 2 ∈ Ico (0 : ℝ) (1 / 2) := by constructor <;> linarith [hα.2]
    have hsin : sin (π * α) = cos (π * (α - 1 / 2)) := by
      rw [show π * α = π * (α - 1 / 2) + π / 2 by ring, sin_add_pi_div_two]
    rw [hsin]
    exact cos_mul_cot_pair_le hh hhπ hu huπ hs
  · have hs : 1 / 2 - α ∈ Ico (0 : ℝ) (1 / 2) := by constructor <;> linarith [hα.1]
    have hsin : sin (π * α) = cos (π * (1 / 2 - α)) := by
      rw [show π * (1 / 2 - α) = -(π * (α - 1 / 2)) by ring, cos_neg,
        ← sin_add_pi_div_two]
      congr 1
      ring
    rw [hsin, show α - 1 / 2 = -(1 / 2 - α) by ring, mul_neg, ← sub_eq_add_neg, sub_neg_eq_add, add_comm]
    exact cos_mul_cot_pair_le hh hhπ hu huπ hs

/-- The sum of absolute Lobatto kernel translates is bounded by its midpoint cotangent sum
at every open-cell phase. Source: focused rederivations, equation `eq:cotpair`. -/
theorem lobattoKernelSum_phase_le {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    lobattoKernelSum n (α * π / n) ≤ lobattoCotangentConstant n := by
  let h : ℝ := π / (2 * n)
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 0 < h := by dsimp [h]; positivity
  have hhπ : h ≤ π / 2 := by dsimp [h]; rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)]; nlinarith [pi_pos]
  have hnh : (n : ℝ) * h = π / 2 := by dsimp [h]; field_simp
  have hpair : ∀ j ∈ range n, sin (π * α) *
      (Real.cot (((j : ℝ) + α) * π / (2 * n)) +
        Real.cot (((j : ℝ) + 1 - α) * π / (2 * n))) ≤
      2 * Real.cot (((j : ℝ) + 1 / 2) * π / (2 * n)) := by
    intro j hj
    have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast mem_range.mp hj
    have hu : h / 2 ≤ ((j : ℝ) + 1 / 2) * h := by nlinarith [show (0 : ℝ) ≤ j by positivity]
    have huπ : ((j : ℝ) + 1 / 2) * h ≤ π / 2 := by nlinarith
    have hb := phase_cot_pair_le hh hhπ hu huπ hα
    have heq1 : ((j : ℝ) + 1 / 2) * h + h * (α - 1 / 2) = ((j : ℝ) + α) * π / (2 * n) := by dsimp [h]; ring
    have heq2 : ((j : ℝ) + 1 / 2) * h - h * (α - 1 / 2) = ((j : ℝ) + 1 - α) * π / (2 * n) := by dsimp [h]; ring
    rw [heq1, heq2] at hb
    simpa only [h, mul_div_assoc] using hb
  have hsum := sum_le_sum hpair
  simp only [← mul_sum] at hsum
  have hb := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1 / (2 * n : ℝ) by positivity)
  rw [lobattoKernelSum_phase hn hα]
  dsimp [lobattoCotangentConstant]
  rw [← mul_assoc, ← mul_assoc] at hb
  have hl : (1 / (2 * n) : ℝ) * sin (π * α) = sin (π * α) / (2 * n) := by ring
  have hr : (1 / (2 * n) : ℝ) * 2 = 1 / n := by ring
  rw [hl, hr] at hb
  exact hb

/-- Every translated finite-cardinal sum has the sharp logarithmic Lobatto bound.
Source: focused polynomial-approximation rederivations, Theorem `thm:lobatto`. -/
theorem lobattoKernelSum_le_log {n : ℕ} (hn : 0 < n) (t : ℝ) :
    lobattoKernelSum n t ≤ 1 + (2 / π) * log ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) < n := by positivity
  obtain ⟨y, hy, heq⟩ := (lobattoKernelSum_periodic hn).exists_mem_Ico₀
    (show 0 < π / n by positivity) t
  rw [heq]
  by_cases hy0 : y = 0
  · rw [hy0, lobattoKernelSum_zero hn]
    have hlog : 0 ≤ log ((n : ℝ) + 1) := log_nonneg (by
      have hN : (0 : ℝ) ≤ n := by positivity
      linarith)
    have hpos : 0 ≤ (2 / π) * log ((n : ℝ) + 1) := mul_nonneg (by positivity) hlog
    linarith
  let α : ℝ := y * n / π
  have hα : α ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (mul_pos (lt_of_le_of_ne hy.1 (Ne.symm hy0)) hn0) pi_pos
    · dsimp [α]
      rw [div_lt_one pi_pos, ← lt_div_iff₀ hn0]
      exact hy.2
  have hangle : α * π / n = y := by dsimp [α]; field_simp
  rw [← hangle]
  exact (lobattoKernelSum_phase_le hn hα).trans (lobattoCotangentConstant_le_log hn)

end NLAlib
