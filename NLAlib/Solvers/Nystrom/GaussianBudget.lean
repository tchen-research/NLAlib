import NLAlib.LowRank.Nystrom.GaussianResidual
import NLAlib.Matrix.Spectral.EffectiveDimension
import NLAlib.Solvers.Nystrom.Condition
import NLAlib.Matrix.Spectral.CourantFischer

/-!
# Effective-dimension budget for the native Gaussian Nyström residual

At the FTU width `2 ceil(3 d_eff / 2)+1`, the refined spectral residual is
bounded by a universal multiple of the regularization. This is a finite
spectral-sum argument and includes arbitrary matrix rank.
Source: Frangella--Tropp--Udell 2023, Theorem 5.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder
namespace NLAlib

/-- Effective dimension of a PSD real matrix, expressed by its nonnegative
singular values. For positive regularization this equals the usual ridge trace. -/
def nystromEffectiveDimension {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) : ℝ :=
  effectiveDimensionOfSpectrum (fun i : Fin n => singularValues A i) μ

/-- Native spectral tail controlled by effective dimension at every integer cutoff. -/
theorem nuclearNorm_sub_truncatedSVD_le_mul_nystromEffectiveDimension
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {μ : ℝ} (hμ : 0 < μ)
    (k : ℕ) (hk : nystromEffectiveDimension A μ ≤ k) :
    nuclearNorm (A - truncatedSVD A k) ≤ μ * nystromEffectiveDimension A μ := by
  rw [nuclearNorm_sub_truncatedSVD_eq_sum]
  have he : (∑ i : Fin (Fintype.card (Fin n)), if k ≤ i.val then singularValues A i else 0) =
      ∑ i : Fin n, if k ≤ i.val then singularValues A i else 0 :=
    Fintype.sum_equiv (finCongr (Fintype.card_fin n)) _ _ (fun _ => rfl)
  rw [he]
  have ht := sum_filter_ge_le_mul_effectiveDimensionOfSpectrum
    (fun i : Fin n => singularValues A i) (fun i => singularValues_nonneg A i)
    (fun i j hij => singularValues_antitone A hij) hμ k hk
  simpa only [Fintype.card_fin, Finset.sum_filter, nystromEffectiveDimension] using ht

/-- Every Nyström singular value is bounded by the corresponding original PSD
eigenvalue. The statement permits deficient and zero sketches. -/
theorem singularValues_nystrom_le {n t : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (Ω : Matrix (Fin n) (Fin t) ℝ) (j : Fin n) :
    singularValues (nystrom A Ω) j ≤ singularValues A j := by
  have hB := posSemidef_nystrom hA Ω
  let j' : Fin (Fintype.card (Fin n)) := ⟨j.val, by simp⟩
  rw [singularValues_eq_eigenvalues₀_of_posSemidef hB j',
    singularValues_eq_eigenvalues₀_of_posSemidef hA j']
  exact Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_of_le hB.isHermitian
    hA.isHermitian (Matrix.le_iff.mpr (posSemidef_sub_nystrom hA Ω)) j'

/-- A head cutoff at least `3 d_eff / 2` controls the next eigenvalue by `2μ`. -/
theorem singularValues_le_two_mul_of_nystromEffectiveDimension_le
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {μ : ℝ} (hμ : 0 < μ)
    (k : ℕ) (hkn : k < n) (hk : 3 * nystromEffectiveDimension A μ / 2 ≤ k) :
    singularValues A k ≤ 2 * μ := by
  apply apply_le_mul_of_effectiveDimensionOfSpectrum_le
    (fun i : Fin n => singularValues A i) (fun i => singularValues_nonneg A i)
    (fun i j hij => singularValues_antitone A hij) hμ (by norm_num : (0 : ℝ) < 2)
    (⟨k, hkn⟩ : Fin n)
  change (1 + 1 / (2 : ℝ)) * nystromEffectiveDimension A μ ≤ (k : ℝ) + 1
  linarith

/-- The floor of the actual FTU preconditioner is at most `μ` at width `2k+1`
when the integer head cutoff dominates the effective dimension. -/
theorem singularValues_nystrom_floor_le_regularization
    {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ) (hwidth : 2 * k + 1 ≤ n)
    (hk : nystromEffectiveDimension A μ ≤ k)
    (Ω : Matrix (Fin n) (Fin (2 * k + 1)) ℝ) :
    singularValues (nystrom A Ω) (2 * k) ≤ μ := by
  apply (singularValues_nystrom_le hA Ω ⟨2*k, by omega⟩).trans
  have h := apply_le_mul_of_effectiveDimensionOfSpectrum_le
    (fun i : Fin n => singularValues A i) (fun i => singularValues_nonneg A i)
    (fun i j hij => singularValues_antitone A hij) hμ (by norm_num : (0 : ℝ) < 1)
    (⟨2*k, by omega⟩ : Fin n) (by
      change (1 + 1 / (1 : ℝ)) * nystromEffectiveDimension A μ ≤ ((2*k : ℕ) : ℝ) + 1
      push_cast
      linarith)
  simpa using h

/-- At the FTU head/oversampling ratio, the actual Gaussian Nyström residual has
an integrable spectral norm bounded in expectation by `(6+2e²)μ`. The finite
cutoff assumptions are implied by `k=ceil(3 d_eff/2)>0`.
atlas: nystrom-pcg (partial) -/
theorem integrable_and_integral_specNorm_sub_nystrom_le_of_effectiveDimension
    {Ωs : Type*} [MeasurableSpace Ωs] {ν : Measure Ωs}
    {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ) (hk0 : 0 < k) (hkn : k < n)
    (hk : 3 * nystromEffectiveDimension A μ / 2 ≤ k)
    (Ω : Ωs → Matrix (Fin n) (Fin (k + (k + 1))) ℝ)
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin (k + (k + 1)))) ν) :
    Integrable (fun ω => specNorm (A - nystrom A (Ω ω))) ν ∧
      ∫ ω, specNorm (A - nystrom A (Ω ω)) ∂ν ≤
        (6 + 2 * Real.exp 1 ^ 2) * μ := by
  obtain ⟨hi, hb⟩ := integrable_and_integral_specNorm_sub_nystrom_le hA
    (by omega : 2 ≤ k+1) hkn Ω hΩ
  have hD : 0 ≤ nystromEffectiveDimension A μ := by
    unfold nystromEffectiveDimension effectiveDimensionOfSpectrum
    exact Finset.sum_nonneg fun i _ => div_nonneg (singularValues_nonneg A i)
      (add_nonneg (singularValues_nonneg A i) hμ.le)
  have hDk : nystromEffectiveDimension A μ ≤ k := by linarith
  have htail := nuclearNorm_sub_truncatedSVD_le_mul_nystromEffectiveDimension A hμ k hDk
  have hnext := singularValues_le_two_mul_of_nystromEffectiveDimension_le A hμ k hkn hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hcoef : Real.exp 1 ^ 2 * (2 * (k : ℝ) + (k + 1)) / (k + 1) ^ 2 ≤
      3 * Real.exp 1 ^ 2 / k := by
    rw [div_le_div_iff₀ (by positivity) hkR]
    nlinarith [sq_nonneg (Real.exp 1)]
  have hco0 : 0 ≤ Real.exp 1 ^ 2 * (2 * (k : ℝ) + (k + 1)) / (k + 1) ^ 2 := by positivity
  have hnuc := nuclearNorm_nonneg (A - truncatedSVD A k)
  have ht1 := mul_le_mul_of_nonneg_left hcoef hnuc
  have ht2 := mul_le_mul_of_nonneg_right htail (show 0 ≤ 3 * Real.exp 1 ^ 2 / k by positivity)
  have ht3 : μ * nystromEffectiveDimension A μ * (3 * Real.exp 1 ^ 2 / k) ≤
      2 * Real.exp 1 ^ 2 * μ := by
    rw [← mul_div_assoc, div_le_iff₀ hkR]
    have hh := mul_le_mul_of_nonneg_left
      (show 3 * nystromEffectiveDimension A μ ≤ 2 * (k : ℝ) by linarith)
      (show 0 ≤ μ * Real.exp 1 ^ 2 by positivity)
    nlinarith only [hh]
  refine ⟨hi, hb.trans ?_⟩
  push_cast
  rw [show ((k : ℝ) + 1 - 1) = k by ring, mul_div_cancel_right₀ (2 : ℝ) (ne_of_gt hkR)]
  nlinarith [ht1.trans (ht2.trans ht3)]

end NLAlib
