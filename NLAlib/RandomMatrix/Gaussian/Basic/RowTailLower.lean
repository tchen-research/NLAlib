import NLAlib.RandomMatrix.Gaussian.Basic.RowMixedNorm
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricRowEnergyLower

/-!
# Scalar Gaussian lower tails inside the actual mixed row norm

A largest profile coefficient supplies one actual Gaussian coordinate.
Its absolute value is bounded by the Euclidean row norm, and hence by
every mixed row norm. This provides the lower tail and mean-to-scale
ratio needed for the full Gaussian Schatten-row tail comparison.
Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Section 3.2.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
private theorem exists_abs_entry_eq_profile_scale (b : Matrix ι ι ℝ)
    (hm : 0 < ‖fun ij : ι × ι => b ij.1 ij.2‖) :
    ∃ i j, |b i j| = ‖fun ij : ι × ι => b ij.1 ij.2‖ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      have heq : (fun ij : ι × ι => b ij.1 ij.2) = 0 := by
        funext ij
        exact isEmptyElim ij.1
      simp only [heq, norm_zero, lt_self_iff_false] at hm
  | inr h =>
      obtain ⟨e, he⟩ := exists_eq_ciSup_of_finite (f := fun ij : ι × ι => |b ij.1 ij.2|)
      have hnorm : ‖fun ij : ι × ι => b ij.1 ij.2‖ ≤ |b e.1 e.2| := by
        apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
        intro ij
        rw [Real.norm_eq_abs, he]
        exact le_ciSup (Set.finite_range (fun ij : ι × ι => |b ij.1 ij.2|)).bddAbove ij
      have hrev : |b e.1 e.2| ≤ ‖fun ij : ι × ι => b ij.1 ij.2‖ := by
        simpa only [Real.norm_eq_abs] using
          norm_le_pi_norm (fun ij : ι × ι => b ij.1 ij.2) e
      exact ⟨e.1, e.2, le_antisymm hrev hnorm⟩

/-- The expected actual mixed row norm uniformly dominates the largest
profile coefficient for every native exponent at least two, including infinity. -/
theorem gaussianAbsoluteLowerConstant_mul_profile_scale_le_integral_rowMixedNorm
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) {p : ℝ≥0∞} (hp : 2 ≤ p) :
    gaussianAbsoluteLowerConstant * ‖fun ij : ι × ι => b ij.1 ij.2‖ ≤
      ∫ G, rowMixedNorm (symmetricGaussianMatrix b G) p ∂gaussianMatrix ι ι := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hcap : ‖fun ij : ι × ι => b ij.1 ij.2‖ ≤ rowMixedNorm b p := by
    apply (pi_norm_le_iff_of_nonneg (rowMixedNorm_nonneg _ _)).mpr
    intro ij
    exact norm_entry_le_rowMixedNorm b hp1 ij.1 ij.2
  exact (mul_le_mul_of_nonneg_left hcap gaussianAbsoluteLowerConstant_pos.le).trans
    (gaussianAbsoluteLowerConstant_mul_rowMixedNorm_le_integral b hb hp1)

/-- One largest actual Gaussian entry gives a scalar Gaussian lower tail
inside every native mixed row norm. No independence between rows is used. -/
theorem exp_neg_sq_div_sqrt_two_pi_le_measure_rowMixedNorm_symmetricGaussianMatrix
    (b : Matrix ι ι ℝ) (hb : b.IsSymm) {p : ℝ≥0∞} (hp : 2 ≤ p)
    (hm : 0 < ‖fun ij : ι × ι => b ij.1 ij.2‖) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-1) / Real.sqrt (2 * Real.pi) *
      Real.exp (-(t / ‖fun ij : ι × ι => b ij.1 ij.2‖) ^ 2) ≤
      (gaussianMatrix ι ι).real {G | t ≤ rowMixedNorm (symmetricGaussianMatrix b G) p} := by
  let m := ‖fun ij : ι × ι => b ij.1 ij.2‖
  obtain ⟨i, j, hij⟩ := exists_abs_entry_eq_profile_scale b hm
  have hlaw := (measurePreserving_gaussianMatrix_entry (max i j) (min i j)).hasLaw
  have hmeasure := hlaw.measureReal_eq
    (measurableSet_le measurable_const measurable_abs : MeasurableSet {x : ℝ | t / m ≤ |x|})
  have hlow := exp_neg_sq_div_sqrt_two_pi_le_gaussianReal_abs_tail (t / m)
    (div_nonneg ht hm.le)
  rw [← hmeasure] at hlow
  apply hlow.trans
  apply measureReal_mono ?_ (by finiteness)
  intro G hG
  have hx := norm_entry_le_rowMixedNorm (symmetricGaussianMatrix b G)
    (le_trans (by norm_num) hp) i j
  rw [Real.norm_eq_abs] at hx
  rw [symmetricGaussianMatrix_apply_of_isSymm b hb, abs_mul, hij] at hx
  exact ((div_le_iff₀ hm).mp hG).trans (by simpa only [mul_comm] using hx)

end NLAlib
