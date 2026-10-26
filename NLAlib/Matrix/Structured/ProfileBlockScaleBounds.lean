import NLAlib.Matrix.Structured.ProfileBlockBounds
import NLAlib.Matrix.Structured.ProfileRearrangementScalarBounds

/-!
# Summable entry scales of the diagonal profile blocks

The initial block uses the maximum row-energy scale; all later blocks use
the logarithmic row thresholds. Their sum is dimension free.
-/

noncomputable section
namespace NLAlib

/-- Entry scale of a supporting profile block, with a separate initial block. -/
def profileBlockEntryBound (a b : ℝ) : ℕ → ℝ
  | 0 => a
  | k + 1 => b / Real.sqrt (Real.log (profilePreviousCutoff k))

/-- Every supporting block entry scale is nonnegative. -/
theorem profileBlockEntryBound_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (t : ℕ) :
    0 ≤ profileBlockEntryBound a b t := by
  cases t with
  | zero => exact ha
  | succ k => exact div_nonneg hb (Real.sqrt_nonneg _)

/-- A symmetric square-dominated profile mask inherits the prescribed entry
bound on each supporting block. -/
theorem profileBlockPart_sq_le_entryBound_sq
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hdom : ∀ i j, B i j ^ 2 ≤ A i j ^ 2)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA0 : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ a ^ 2)
    (hthreshold : ∀ k i j, profileCutoff k ≤ i.val →
      A i j ≤ b / Real.sqrt (Real.log (profilePreviousCutoff k)))
    (t : ℕ) (i j : Fin n) :
    profileBlockPart B t i j ^ 2 ≤ profileBlockEntryBound a b t ^ 2 := by
  classical
  cases t with
  | zero => exact (profileBlockPart_sq_le B 0 i j).trans ((hdom i j).trans
      ((Finset.single_le_sum (fun l _ => sq_nonneg (A i l)) (Finset.mem_univ j)).trans
        (hrow i)))
  | succ k =>
      have hm := profileBlockEntryBound_nonneg ha hb (k + 1)
      unfold profileBlockPart
      split_ifs with hin
      · have hsmall := hthreshold k i j hin.1.1
        change B i j ^ 2 ≤ (b / Real.sqrt (Real.log (profilePreviousCutoff k))) ^ 2
        exact (hdom i j).trans (by nlinarith [hA0 i j])
      · simp [sq_nonneg]

/-- All the block entry scales have a uniform finite-sum bound. -/
theorem sum_profileBlockEntryBound_le {a b : ℝ} (hb : 0 ≤ b) (L : ℕ) :
    (∑ t ∈ Finset.range (L + 1), profileBlockEntryBound a b t) ≤ a + 8 * b := by
  rw [Finset.sum_range_succ']
  simp only [profileBlockEntryBound]
  simp only [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  have h := sum_one_div_sqrt_log_previous_le_eight L
  simp only [one_div] at h
  nlinarith [mul_le_mul_of_nonneg_left h hb]

end NLAlib
