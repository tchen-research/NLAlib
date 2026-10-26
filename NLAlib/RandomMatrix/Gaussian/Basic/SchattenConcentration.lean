import NLAlib.Matrix.Norms.SchattenInvariant
import NLAlib.Matrix.Norms.SchattenComparison
import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfileLipschitz

/-!
# Concentration of every Gaussian Schatten norm

The native Schatten norm is Frobenius Lipschitz for all exponents at least
two, including infinity. Applied to the actual symmetric profile ensemble,
this gives the same entry-scale concentration as the mixed row norm.
Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Section 3.2.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The difference of two native Schatten norms of exponent at least two
is bounded by the Frobenius norm of the matrix difference. -/
theorem abs_schattenNorm_sub_le_frobNorm (A B : Matrix ι ι ℝ)
    {p : ℝ≥0∞} (hp : 2 ≤ p) :
    |schattenNorm A p - schattenNorm B p| ≤ frobNorm (A - B) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hnorm (M : Matrix ι ι ℝ) : schattenNorm M p ≤ frobNorm M := by
    simpa only [schattenNorm_two] using schattenNorm_le_of_le M (by norm_num) hp
  have hAB := (schattenNorm_add_le (A - B) B hp1).trans
    (add_le_add (hnorm (A - B)) le_rfl)
  have hBA := (schattenNorm_add_le (B - A) A hp1).trans
    (add_le_add (hnorm (B - A)) le_rfl)
  rw [sub_add_cancel] at hAB hBA
  have hf : frobNorm (B - A) = frobNorm (A - B) := by
    rw [show B - A = -(A - B) by abel, frobNorm_neg]
  rw [hf] at hBA
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual symmetric Gaussian native Schatten norm has Lipschitz
constant `sqrt 2 * m` whenever every entry coefficient has magnitude at most `m`. -/
theorem abs_schattenNorm_symmetricGaussianMatrix_sub_le
    (b : Matrix ι ι ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hcap : ∀ i j, b i j ^ 2 ≤ m ^ 2) {p : ℝ≥0∞} (hp : 2 ≤ p)
    (G H : Matrix ι ι ℝ) :
    |schattenNorm (symmetricGaussianMatrix b G) p -
      schattenNorm (symmetricGaussianMatrix b H) p| ≤
        Real.sqrt 2 * m * frobNorm (G - H) :=
  (abs_schattenNorm_sub_le_frobNorm _ _ hp).trans
    (frobNorm_symmetricGaussianMatrix_sub_le b hm hcap G H)

/-- The centered actual Gaussian native Schatten norm is sub-Gaussian
with proxy `2 m²`, uniformly over all exponents at least two, including infinity. -/
theorem hasSubgaussianMGF_schattenNorm_symmetricGaussianMatrix
    (b : Matrix ι ι ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hcap : ∀ i j, b i j ^ 2 ≤ m ^ 2) {p : ℝ≥0∞} (hp : 2 ≤ p) :
    HasSubgaussianMGF
      (fun G => schattenNorm (symmetricGaussianMatrix b G) p -
        ∫ H, schattenNorm (symmetricGaussianMatrix b H) p ∂gaussianMatrix ι ι)
      ⟨2 * m ^ 2, by positivity⟩ (gaussianMatrix ι ι) := by
  have hproxy : (Real.sqrt 2 * m) ^ 2 = 2 * m ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [hproxy] using hasSubgaussianMGF_of_lipschitz_gaussianMatrix
    (fun G => schattenNorm (symmetricGaussianMatrix b G) p) (Real.sqrt 2 * m)
    (mul_nonneg (Real.sqrt_nonneg _) hm)
    (abs_schattenNorm_symmetricGaussianMatrix_sub_le b hm hcap hp)

/-- Every native Schatten norm of the actual finite Gaussian profile
ensemble is integrable when its exponent is at least two. -/
theorem integrable_schattenNorm_symmetricGaussianMatrix
    (b : Matrix ι ι ℝ) {p : ℝ≥0∞} (hp : 2 ≤ p) :
    Integrable (fun G => schattenNorm (symmetricGaussianMatrix b G) p)
      (gaussianMatrix ι ι) := by
  let m := ‖fun ij : ι × ι => b ij.1 ij.2‖
  have hm : 0 ≤ m := norm_nonneg _
  have hcap (i j : ι) : b i j ^ 2 ≤ m ^ 2 := by
    have h : |b i j| ≤ m := by
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm (fun ij : ι × ι => b ij.1 ij.2) (i, j)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  exact integrable_of_lipschitz_gaussianMatrix _ (Real.sqrt 2 * m)
    (mul_nonneg (Real.sqrt_nonneg _) hm)
    (abs_schattenNorm_symmetricGaussianMatrix_sub_le b hm hcap hp)

end NLAlib
