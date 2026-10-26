import NLAlib.RandomMatrix.Gaussian.Moments.FiniteSupportOperatorMean
import NLAlib.Matrix.Structured.ProfileBlockBounds
import NLAlib.Matrix.Structured.ProfileRearrangementScalarBounds

/-!
# Uniform mean bounds for the diagonal Gaussian profile blocks

The moment parameter `2^(t+1)` absorbs the `t`th supporting block's dimension.
Its square-root factor cancels the logarithmic row threshold, giving one
universal bound for every block, including the initial block.
Source: Latała--van Handel--Youssef (2018), Section 3.2.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- Every diagonal block in the rearrangement has uniformly bounded expected
Gaussian spectral norm. The matrix `B` may be any symmetric entrywise
square-dominated mask of `A`, so this covers both diagonal parts. -/
theorem integral_specNorm_symmetricGaussianMatrix_profileBlockPart_le
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (hdom : ∀ i j, B i j ^ 2 ≤ A i j ^ 2)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA0 : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ a ^ 2)
    (hthreshold : ∀ k i j, profileCutoff k ≤ i.val →
      A i j ≤ b / Real.sqrt (Real.log (profilePreviousCutoff k))) (t : ℕ) :
    (∫ G, specNorm (symmetricGaussianMatrix (profileBlockPart B t) G)
      ∂gaussianMatrix (Fin n) (Fin n)) ≤ 192 * (a + b) := by
  classical
  let S := profileBlockCoordinates n t
  have hcard : S.card ≤ 2 ^ (2 * 2 ^ (t + 1)) :=
    (card_profileBlockCoordinates_le n t).trans
      ((profileNeighborCutoff_lt_cutoff_succ t).le.trans
        (le_of_eq (profileCutoff_succ_eq_two_pow_two_mul t)))
  have hrow' (i : Fin n) : ∑ j, profileBlockPart B t i j ^ 2 ≤ a ^ 2 :=
    (sum_row_sq_profileBlockPart_le B t i).trans
      ((Finset.sum_le_sum fun j _ => hdom i j).trans (hrow i))
  have hzero (i : Fin n) (hi : i ∉ S) (j : Fin n) : profileBlockPart B t i j = 0 :=
    profileBlockPart_eq_zero_of_not_mem B t i hi j
  have hsym := isSymm_profileBlockPart B hB t
  cases t with
  | zero =>
      have hentry (i j : Fin n) : profileBlockPart B 0 i j ^ 2 ≤ a ^ 2 :=
        (profileBlockPart_sq_le B 0 i j).trans ((hdom i j).trans
          ((Finset.single_le_sum (fun l _ => sq_nonneg (A i l)) (Finset.mem_univ j)).trans
            (hrow i)))
      have hmean := integral_specNorm_symmetricGaussianMatrix_le_of_support_card
        (profileBlockPart B 0) hsym S 2 (by omega) (by simpa using hcard)
        ha ha hrow' hentry hzero
      norm_num only [Nat.cast_ofNat] at hmean
      apply hmean.trans
      have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 :=
        (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hsqrt ha]
  | succ k =>
      let m := b / Real.sqrt (Real.log (profilePreviousCutoff k))
      have hm : 0 ≤ m := div_nonneg hb (Real.sqrt_nonneg _)
      have hentry (i j : Fin n) : profileBlockPart B (k + 1) i j ^ 2 ≤ m ^ 2 := by
        unfold profileBlockPart
        split_ifs with hin
        · have hsmall := hthreshold k i j hin.1.1
          exact (hdom i j).trans (by nlinarith [hA0 i j])
        · simp [sq_nonneg]
      have hmean := integral_specNorm_symmetricGaussianMatrix_le_of_support_card
        (profileBlockPart B (k + 1)) hsym S (2 ^ (k + 1 + 1)) (by positivity)
        hcard ha hm hrow' hentry hzero
      apply hmean.trans
      have hfactor : Real.sqrt ((2 ^ (k + 1 + 1) : ℕ) : ℝ) * m ≤ 4 * b := by
        have h := mul_le_mul_of_nonneg_right
          (sqrt_two_pow_div_sqrt_log_previous_le_four k) hb
        simpa only [show k + 1 + 1 = k + 2 by omega, m, div_eq_mul_inv, mul_assoc,
          mul_comm, mul_left_comm] using h
      nlinarith

end NLAlib
