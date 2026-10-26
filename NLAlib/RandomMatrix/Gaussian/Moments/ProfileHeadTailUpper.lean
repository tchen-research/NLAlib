import NLAlib.Matrix.Structured.HeadTailSplit
import NLAlib.RandomMatrix.Gaussian.Basic.ProfileMasks
import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfileLipschitz
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileRealUpper

/-!
# Actual finite-exponent Gaussian head-tail upper bound

A principal tail is controlled by the full real Schatten moment theorem.
The remaining matrix has rank at most twice the head size, so its mean is
controlled by the actual operator mean. No matrix-dimension factor remains
once the head size is chosen exponentially in the exponent.
Source: Latała--van Handel--Youssef (2018), Section 3.2.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

private theorem sample_principalTailPart {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    symmetricGaussianMatrix (principalTailPart A r) G =
      principalTailPart (symmetricGaussianMatrix A G) r := by
  exact symmetricGaussianMatrix_mask
    (fun i j : Fin n => r ≤ i.val ∧ r ≤ j.val) (fun _ _ => and_comm) A G

private theorem sq_principalTailPart_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (i j : Fin n) : principalTailPart A r i j ^ 2 ≤ A i j ^ 2 := by
  unfold principalTailPart
  split_ifs <;> simp [sq_nonneg]

private theorem norm_principalTailPart_row_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (i : Fin n) :
    ‖principalTailPart A r i‖ ≤ if r ≤ i.val then ‖A i‖ else 0 := by
  by_cases hi : r ≤ i.val
  · rw [if_pos hi]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    unfold principalTailPart
    split_ifs
    · exact norm_le_pi_norm (A i) j
    · simp [norm_nonneg]
  · have hz : principalTailPart A r i = 0 := by
      ext j
      simp [principalTailPart, hi]
    simp only [hz, norm_zero, if_neg hi, le_refl]

private theorem integral_schattenNormReal_le_matching_root {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {p : ℝ} (hp : 2 ≤ p) :
    (∫ G, schattenNormReal (symmetricGaussianMatrix A G) p
      ∂gaussianMatrix (Fin n) (Fin n)) ≤
    (∫ G, schattenNormReal (symmetricGaussianMatrix A G) p ^ p
      ∂gaussianMatrix (Fin n) (Fin n)) ^ p⁻¹ := by
  have h := integral_rpow_root_le_of_nonneg_of_le
    (memLp_schattenNormReal_symmetricGaussianMatrix A hp).aestronglyMeasurable
    (fun G => schattenNormReal_nonneg _ _) (by norm_num : (0 : ℝ) < 1)
    (by linarith : (1 : ℝ) ≤ p) (integrable_schattenNormReal_symmetricGaussianMatrix_rpow A hp)
  simpa only [Real.rpow_one, inv_one] using h

/-- The actual Gaussian Schatten mean splits into an operator-mean head
and the sharp variance and row-cap profiles of the principal tail. The head
size `r` is arbitrary and may exceed the dimension; the exponent is any real
number at least two. -/
theorem integral_schattenNormReal_symmetricGaussianMatrix_le_head_tail_moments
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hA0 : ∀ i j, 0 ≤ A i j) (r : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    (∫ G, schattenNormReal (symmetricGaussianMatrix A G) p
      ∂gaussianMatrix (Fin n) (Fin n)) ≤
      2 * (2 * r : ℝ) ^ (1 / p) *
        (∫ G, specNorm (symmetricGaussianMatrix A G) ∂gaussianMatrix (Fin n) (Fin n)) +
      512 * ((∑ i, (∑ j, A i j ^ 2) ^ (p / 2)) ^ p⁻¹ +
        Real.sqrt p * (∑ i : Fin n, ‖principalTailPart A r i‖ ^ p) ^ p⁻¹) := by
  have hp0 : 0 < p := by linarith
  let T := principalTailPart A r
  have hT : T.IsSymm := isSymm_principalTailPart A hA r
  have hT0 (i j : Fin n) : 0 ≤ T i j := by
    dsimp [T, principalTailPart]
    split_ifs
    · exact hA0 i j
    · exact le_rfl
  have hmoment := integral_schattenNorm_symmetricGaussianMatrix_rpow_root_le T hT hT0 hp
  simp only [schattenNorm_ofReal _ hp0.le] at hmoment
  have hvariance : (∑ i, (∑ j, T i j ^ 2) ^ (p / 2)) ^ p⁻¹ ≤
      (∑ i, (∑ j, A i j ^ 2) ^ (p / 2)) ^ p⁻¹ := by
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg
      (Finset.sum_nonneg fun j _ => sq_nonneg _) _) _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => sq_nonneg _)
      (Finset.sum_le_sum fun j _ => sq_principalTailPart_le A r i j) (by positivity)
  have htail := (integral_schattenNormReal_le_matching_root T hp).trans hmoment
  have htail' : (∫ G, schattenNormReal (symmetricGaussianMatrix T G) p
      ∂gaussianMatrix (Fin n) (Fin n)) ≤
      512 * ((∑ i, (∑ j, A i j ^ 2) ^ (p / 2)) ^ p⁻¹ +
        Real.sqrt p * (∑ i : Fin n, ‖T i‖ ^ p) ^ p⁻¹) := by
    apply htail.trans
    gcongr
  have hInt (B : Matrix (Fin n) (Fin n) ℝ) :
      Integrable (fun G => schattenNormReal (symmetricGaussianMatrix B G) p)
        (gaussianMatrix (Fin n) (Fin n)) :=
    (memLp_schattenNormReal_symmetricGaussianMatrix B hp).integrable
      (ENNReal.one_le_ofReal.mpr (by linarith))
  have hpoint (G : Matrix (Fin n) (Fin n) ℝ) :
      schattenNormReal (symmetricGaussianMatrix A G) p ≤
        2 * (2 * r : ℝ) ^ (1 / p) * specNorm (symmetricGaussianMatrix A G) +
          schattenNormReal (symmetricGaussianMatrix T G) p := by
    have hsplit : headTailRemainder (symmetricGaussianMatrix A G) r +
        principalTailPart (symmetricGaussianMatrix A G) r = symmetricGaussianMatrix A G :=
      sub_add_cancel _ _
    calc
      _ = schattenNormReal (headTailRemainder (symmetricGaussianMatrix A G) r +
          principalTailPart (symmetricGaussianMatrix A G) r) p := congrArg
        (fun B => schattenNormReal B p) hsplit.symm
      _ ≤ schattenNormReal (headTailRemainder (symmetricGaussianMatrix A G) r) p +
          schattenNormReal (principalTailPart (symmetricGaussianMatrix A G) r) p :=
        schattenNormReal_add_le _ _ (by linarith)
      _ ≤ _ := by
        rw [← sample_principalTailPart]
        have h := schattenNormReal_headTailRemainder_le (symmetricGaussianMatrix A G) r hp0
        dsimp [T]
        nlinarith
  have hmono := integral_mono
    (f := fun G => schattenNormReal (symmetricGaussianMatrix A G) p)
    (g := fun G => 2 * (2 * r : ℝ) ^ (1 / p) * specNorm (symmetricGaussianMatrix A G) +
      schattenNormReal (symmetricGaussianMatrix T G) p) (hInt A)
    (((integrable_specNorm_symmetricGaussianMatrix_of_finite_profile A).const_mul
      (2 * (2 * r : ℝ) ^ (1 / p))).add (hInt T)) hpoint
  have hsumInt : Integrable (fun G =>
      2 * (2 * r : ℝ) ^ (1 / p) * specNorm (symmetricGaussianMatrix A G))
      (gaussianMatrix (Fin n) (Fin n)) :=
    (integrable_specNorm_symmetricGaussianMatrix_of_finite_profile A).const_mul _
  rw [integral_add hsumInt (hInt T), integral_const_mul] at hmono
  linarith

/-- A useful coarser version uses the original row caps in the tail, even
when a row's largest entry lies in a removed head column. -/
theorem integral_schattenNormReal_symmetricGaussianMatrix_le_head_tail_profiles
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hA0 : ∀ i j, 0 ≤ A i j) (r : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    (∫ G, schattenNormReal (symmetricGaussianMatrix A G) p
      ∂gaussianMatrix (Fin n) (Fin n)) ≤
      2 * (2 * r : ℝ) ^ (1 / p) *
        (∫ G, specNorm (symmetricGaussianMatrix A G) ∂gaussianMatrix (Fin n) (Fin n)) +
      512 * ((∑ i, (∑ j, A i j ^ 2) ^ (p / 2)) ^ p⁻¹ +
        Real.sqrt p * (∑ i : Fin n, if r ≤ i.val then ‖A i‖ ^ p else 0) ^ p⁻¹) := by
  apply (integral_schattenNormReal_symmetricGaussianMatrix_le_head_tail_moments
    A hA hA0 r hp).trans
  have hp0 : 0 < p := by linarith
  have hcaps : (∑ i, ‖principalTailPart A r i‖ ^ p) ^ p⁻¹ ≤
      (∑ i : Fin n, if r ≤ i.val then ‖A i‖ ^ p else 0) ^ p⁻¹ := by
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) _
      (by positivity)
    apply Finset.sum_le_sum
    intro i _
    have h := Real.rpow_le_rpow (norm_nonneg _)
      (norm_principalTailPart_row_le A r i) hp0.le
    split_ifs at h ⊢ with hi
    · exact h
    · simpa only [Real.zero_rpow hp0.ne'] using h
  gcongr

end NLAlib
