import NLAlib.Matrix.Norms.BilinearZeroParameter
import NLAlib.Probability.Free.WordMatrixSpectrum
import NLAlib.Probability.Free.WordNativeMatrixLinearCombination

/-! # The actual zero-weak-variance Gaussian/free comparison

Zero attained bilinear coefficient energy forces every coefficient to
vanish. The actual Gaussian matrix and native free model then have the
same spectrum for every coordinate vector.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

/-- The actual Gaussian and native free spectra have Hausdorff distance
zero whenever the original bilinear weak variance vanishes. This is a
pointwise deterministic equality, including empty matrix dimensions and
coefficient families. Source: the degenerate case of
arXiv:2406.11453v2, Theorem 2.2. -/
theorem hausdorffDist_spectrum_gaussian_wordNative_eq_zero_of_zero_weak
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian) (A : ι → Matrix d d ℂ)
    (hzero : bilinearSquareMass A Finset.univ = 0) (x : ι → ℝ) :
    Metric.hausdorffDist (spectrum ℝ (A₀ + ∑ i, x i • A i))
      (spectrum ℝ (wordNativeMatrixLinearCombination A₀ A)) = 0 := by
  have hA := (bilinearSquareMass_univ_eq_zero_iff A).mp hzero
  have hHerm : ∀ i, (A i).IsHermitian := by
    intro i
    rw [hA]
    exact Matrix.isHermitian_zero
  have hbound := hausdorffDist_spectrum_wordMatrixLinearCombination_mean_le hA₀ A hHerm
  have hbound0 : Metric.hausdorffDist (spectrum ℝ (wordMatrixLinearCombination A₀ A))
      (spectrum ℝ A₀) ≤ 0 := by
    simpa only [hA, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
      specNorm_zero, Real.sqrt_zero, mul_zero] using hbound
  have hs : spectrum ℝ (wordMatrixLinearCombination A₀ A) =
      spectrum ℝ (wordNativeMatrixLinearCombination A₀ A) := by
    simpa only [toPiLp_wordNativeMatrixLinearCombination] using!
      CStarMatrix.spectrum_real_toPiLpStarAlgHom
        (D := d) (H := WordHilbertSpace ι)
        (isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hHerm)
  have hg : A₀ + ∑ i, x i • A i = A₀ := by
    simp only [hA, smul_zero, Finset.sum_const_zero, add_zero]
  rw [hg, ← hs, Metric.hausdorffDist_comm]
  exact le_antisymm hbound0 Metric.hausdorffDist_nonneg

end NLAlib
