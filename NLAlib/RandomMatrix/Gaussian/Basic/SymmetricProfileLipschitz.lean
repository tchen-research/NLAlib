import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfile
import NLAlib.Matrix.Norms.SpectralNormBounds
import NLAlib.RandomMatrix.Gaussian.Basic.MeanDeviation

/-!
# Lipschitz constants for symmetric Gaussian profile norms

Copying a lower-triangular coordinate to its symmetric partner costs at most
`sqrt 2` in Frobenius norm. Consequently the spectral norm of the actual
profile ensemble is `sqrt 2` times its largest entry scale Lipschitz.
-/

noncomputable section
open MeasureTheory
namespace NLAlib

/-- The symmetric profile sample map is Frobenius Lipschitz with constant
`sqrt 2 * m` when all profile entries have magnitude at most `m`. -/
theorem frobNorm_symmetricGaussianMatrix_sub_le
    {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Matrix ι ι ℝ) {m : ℝ}
    (hm : 0 ≤ m) (hcap : ∀ i j, b i j ^ 2 ≤ m ^ 2) (G H : Matrix ι ι ℝ) :
    frobNorm (symmetricGaussianMatrix b G - symmetricGaussianMatrix b H) ≤
      Real.sqrt 2 * m * frobNorm (G - H) := by
  classical
  let D := G - H
  have hpoint (i j : ι) :
      ((symmetricGaussianMatrix b G - symmetricGaussianMatrix b H) i j) ^ 2 ≤
        m ^ 2 * (D i j ^ 2 + D j i ^ 2) := by
    have hcopy : D (max i j) (min i j) ^ 2 ≤ D i j ^ 2 + D j i ^ 2 := by
      by_cases hij : i ≤ j
      · simp only [max_eq_right hij, min_eq_left hij]; nlinarith [sq_nonneg (D i j)]
      · simp only [max_eq_left (le_of_not_ge hij), min_eq_right (le_of_not_ge hij)]
        nlinarith [sq_nonneg (D j i)]
    calc
      _ = b (max i j) (min i j) ^ 2 * D (max i j) (min i j) ^ 2 := by
        simp only [symmetricGaussianMatrix, Matrix.sub_apply, Matrix.of_apply, D]
        ring
      _ ≤ m ^ 2 * D (max i j) (min i j) ^ 2 :=
        mul_le_mul_of_nonneg_right (hcap _ _) (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hcopy (sq_nonneg m)
  have hsum : frobSq (symmetricGaussianMatrix b G - symmetricGaussianMatrix b H) ≤
      2 * m ^ 2 * frobSq D := by
    rw [frobSq_eq_sum_sq, frobSq_eq_sum_sq]
    apply (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j).trans
    apply le_of_eq
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_comm (f := fun i j => D j i ^ 2)]
    ring
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hleft := frobNorm_sq (symmetricGaussianMatrix b G - symmetricGaussianMatrix b H)
  have hright := frobNorm_sq D
  have hnonneg : 0 ≤ Real.sqrt 2 * m * frobNorm D :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hm) (frobNorm_nonneg _)
  have hsq : (Real.sqrt 2 * m * frobNorm D) ^ 2 = 2 * m ^ 2 * frobSq D := by
    rw [mul_pow, mul_pow, hsqrt, hright]
  change frobNorm _ ≤ Real.sqrt 2 * m * frobNorm D
  nlinarith [frobNorm_nonneg (symmetricGaussianMatrix b G - symmetricGaussianMatrix b H)]

/-- The spectral norm of the actual symmetric Gaussian sample has
Frobenius Lipschitz constant `sqrt 2 * m`. -/
theorem abs_specNorm_symmetricGaussianMatrix_sub_le
    {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Matrix ι ι ℝ) {m : ℝ}
    (hm : 0 ≤ m) (hcap : ∀ i j, b i j ^ 2 ≤ m ^ 2) (G H : Matrix ι ι ℝ) :
    |specNorm (symmetricGaussianMatrix b G) - specNorm (symmetricGaussianMatrix b H)| ≤
      Real.sqrt 2 * m * frobNorm (G - H) :=
  (abs_specNorm_sub_specNorm_le_frobNorm _ _).trans
    (frobNorm_symmetricGaussianMatrix_sub_le b hm hcap G H)

/-- The actual symmetric Gaussian profile spectral norm is integrable for
every finite real profile, including nonsymmetric and zero profiles. -/
theorem integrable_specNorm_symmetricGaussianMatrix_of_finite_profile
    {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Matrix ι ι ℝ) :
    Integrable (fun G => specNorm (symmetricGaussianMatrix b G)) (gaussianMatrix ι ι) := by
  let m := ‖fun ij : ι × ι => b ij.1 ij.2‖
  have hm : 0 ≤ m := norm_nonneg _
  have hcap (i j : ι) : b i j ^ 2 ≤ m ^ 2 := by
    have h : |b i j| ≤ m := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun ij : ι × ι => b ij.1 ij.2) (i, j)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  exact integrable_of_lipschitz_gaussianMatrix _ (Real.sqrt 2 * m)
    (mul_nonneg (Real.sqrt_nonneg _) hm)
    (abs_specNorm_symmetricGaussianMatrix_sub_le b hm hcap)

end NLAlib
