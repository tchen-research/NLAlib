import NLAlib.RandomMatrix.Gaussian.Moments.ProfileBlockOperatorMeans
import NLAlib.RandomMatrix.Gaussian.Basic.MeanDeviation
import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfileLipschitz
import NLAlib.Matrix.Structured.ProfileBlockScaleBounds

/-!
# Uniform expected maximum of the profile block norms

The block means are uniformly bounded and their Lipschitz constants have a
bounded sum. Mean absolute Gaussian deviations therefore control the actual
maximum without a factor for the number of blocks or an independence assumption.
Source: Latała--van Handel--Youssef (2018), Section 3.2.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- The expected maximum of all supporting Gaussian block norms is bounded
uniformly in the ambient dimension and the number of blocks. -/
theorem integral_iSup_specNorm_symmetricGaussianMatrix_profileBlockPart_le
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (hdom : ∀ i j, B i j ^ 2 ≤ A i j ^ 2)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA0 : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ a ^ 2)
    (hthreshold : ∀ k i j, profileCutoff k ≤ i.val →
      A i j ≤ b / Real.sqrt (Real.log (profilePreviousCutoff k))) :
    (∫ G, ⨆ t : Fin (n + 1),
      specNorm (symmetricGaussianMatrix (profileBlockPart B t.val) G)
      ∂gaussianMatrix (Fin n) (Fin n)) ≤ 224 * (a + b) := by
  classical
  let L : Fin (n + 1) → ℝ := fun t => Real.sqrt 2 * profileBlockEntryBound a b t.val
  have hL (t : Fin (n + 1)) : 0 ≤ L t := mul_nonneg (Real.sqrt_nonneg _)
    (profileBlockEntryBound_nonneg ha hb _)
  have hsum : (∑ t, L t) ≤ Real.sqrt 2 * (a + 8 * b) := by
    simp only [L, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    simpa only [Fin.sum_univ_eq_sum_range] using sum_profileBlockEntryBound_le hb n
  have hmean := integral_iSup_le_mean_add_two_mul_sum_of_lipschitz_gaussianMatrix
    (fun t : Fin (n + 1) => fun G =>
      specNorm (symmetricGaussianMatrix (profileBlockPart B t.val) G)) L hL
    (fun t G H => abs_specNorm_symmetricGaussianMatrix_sub_le _
      (profileBlockEntryBound_nonneg ha hb t.val)
      (profileBlockPart_sq_le_entryBound_sq A B hdom ha hb hA0 hrow hthreshold t.val) G H)
    (fun t => integral_specNorm_symmetricGaussianMatrix_profileBlockPart_le
      A B hB hdom ha hb hA0 hrow hthreshold t.val)
  apply hmean.trans
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 :=
    (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr (by norm_num)
  have hsum' : ∑ t, L t ≤ 2 * (a + 8 * b) :=
    hsum.trans (mul_le_mul_of_nonneg_right hsqrt (by positivity))
  linarith

end NLAlib
