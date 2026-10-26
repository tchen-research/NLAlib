import NLAlib.Matrix.Structured.HeadTailSplit
import NLAlib.RandomMatrix.Gaussian.Basic.ProfileMasks
import NLAlib.RandomMatrix.Gaussian.Basic.RowMixedNorm
import NLAlib.ForMathlib.Analysis.ExponentialHeadCutoff

/-!
# Actual principal Gaussian tails and mixed row norms

Principal masks commute with the canonical Gaussian sample, decrease every
mixed row norm, and have entry scale bounded by the first remaining sorted
row cap. At an exponential cutoff this scale is controlled by the
logarithmically weighted row envelope.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib

/-- A principal tail mask commutes with the actual Gaussian sample. -/
theorem symmetricGaussianMatrix_principalTailPart {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    symmetricGaussianMatrix (principalTailPart A r) G =
      principalTailPart (symmetricGaussianMatrix A G) r :=
  symmetricGaussianMatrix_mask (fun i j : Fin n => r ≤ i.val ∧ r ≤ j.val)
    (fun _ _ => and_comm) A G

/-- Every native mixed row norm decreases under principal-tail masking. -/
theorem rowMixedNorm_principalTailPart_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    rowMixedNorm (principalTailPart A r) p ≤ rowMixedNorm A p := by
  apply rowMixedNorm_le_of_rowSq_le _ _ hp
  intro i
  apply Finset.sum_le_sum
  intro j _
  unfold principalTailPart
  split_ifs <;> simp [sq_nonneg]

/-- The actual mean mixed row norm of a principal Gaussian tail is bounded
by that of the original profile. -/
theorem integral_rowMixedNorm_symmetricGaussianMatrix_principalTailPart_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) {p : ℝ≥0∞} (hp : 2 ≤ p) :
    (∫ G, rowMixedNorm (symmetricGaussianMatrix (principalTailPart A r) G) p
      ∂gaussianMatrix (Fin n) (Fin n)) ≤
    (∫ G, rowMixedNorm (symmetricGaussianMatrix A G) p ∂gaussianMatrix (Fin n) (Fin n)) := by
  apply integral_mono (integrable_rowMixedNorm_symmetricGaussianMatrix _ hp)
    (integrable_rowMixedNorm_symmetricGaussianMatrix _ hp)
  intro G
  change rowMixedNorm (symmetricGaussianMatrix (principalTailPart A r) G) p ≤
    rowMixedNorm (symmetricGaussianMatrix A G) p
  rw [symmetricGaussianMatrix_principalTailPart]
  exact rowMixedNorm_principalTailPart_le _ r (le_trans (by norm_num) hp)

/-- The first remaining row cap, with zero value if the cutoff has already
covered the matrix. -/
def principalTailEntryBound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : ℝ :=
  if hr : r < n then ‖A ⟨r, hr⟩‖ else 0

/-- The principal-tail entry bound is nonnegative. -/
theorem principalTailEntryBound_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    0 ≤ principalTailEntryBound A r := by
  unfold principalTailEntryBound
  split_ifs <;> positivity

/-- Sorting the row caps makes the first remaining cap a uniform entry bound
for the actual principal tail. -/
theorem principalTailPart_sq_le_entryBound_sq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hanti : Antitone (fun i => ‖A i‖))
    (r : ℕ) (i j : Fin n) :
    principalTailPart A r i j ^ 2 ≤ principalTailEntryBound A r ^ 2 := by
  by_cases hr : r < n
  · rw [principalTailEntryBound, dif_pos hr]
    unfold principalTailPart
    split_ifs with hij
    · have he : |A i j| ≤ ‖A i‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (A i) j
      have h : |A i j| ≤ ‖A ⟨r, hr⟩‖ :=
        he.trans (hanti (show (⟨r, hr⟩ : Fin n) ≤ i from hij.1))
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    · simp
  · have hi : ¬ r ≤ i.val := by omega
    simp [principalTailPart, principalTailEntryBound, hr, hi]

/-- At the exponential cutoff, the tail entry scale times `sqrt p` is
bounded by any logarithmic row envelope of the sorted profile. -/
theorem sqrt_mul_principalTailEntryBound_ceil_exp_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {b p : ℝ} (hb : 0 ≤ b)
    (hweight : ∀ i, ‖A i‖ * Real.sqrt (Real.log (i.val + 1)) ≤ b) :
    Real.sqrt p * principalTailEntryBound A ⌈Real.exp p⌉₊ ≤ b := by
  by_cases hr : ⌈Real.exp p⌉₊ < n
  · rw [principalTailEntryBound, dif_pos hr]
    have h := mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (Real.le_log_ceil_exp_add_one p)) (norm_nonneg (A ⟨_, hr⟩))
    have hw := hweight ⟨_, hr⟩
    nlinarith
  · simp only [principalTailEntryBound, dif_neg hr, mul_zero]
    exact hb

end NLAlib
