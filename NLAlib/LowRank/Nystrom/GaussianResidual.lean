/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.LowRank.RangeFinding.GaussianBlockMoment
import NLAlib.LowRank.Nystrom.Structural
import NLAlib.Matrix.Measurability.GramPseudoinverse

/-!
# Refined Gaussian Nyström spectral error

The squared HMT range-finder estimate applied to a Gram factor and conditioned
Gaussian second moments gives the residual estimate used by FTU. The theorem
uses the actual Nyström matrix and includes integrability, every matrix rank,
and a zero-width head. Source: Frangella–Tropp–Udell 2023, Theorem 5.1 proof;
Halko–Martinsson–Tropp 2011, Theorem 9.1.
Atlas: `nystrom-pcg` (randomized residual kernel).
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder
namespace NLAlib

/-- The actual Nyström formula is measurable at every rank. -/
theorem measurable_nystrom {n t : Type*} [Fintype n] [Fintype t]
    [DecidableEq n] [DecidableEq t] (A : Matrix n n ℝ) :
    Measurable (nystrom A : Matrix n t ℝ → Matrix n n ℝ) := by
  unfold nystrom
  exact ((measurable_const.matrix_mul measurable_id).matrix_mul
    (measurable_moorePenroseInverse.comp
      ((Matrix.measurable_transpose.matrix_mul measurable_const).matrix_mul measurable_id))).matrix_mul
        (Matrix.measurable_transpose.matrix_mul measurable_const)

/-- **Refined Gaussian Nyström spectral bound, Gram-factor form.** All matrix ranks
are covered; the head need not be invertible. The Gaussian sketch and pseudoinverse
are the native constructions, without a supplied moment or range certificate. -/
theorem integrable_and_integral_specNorm_sub_nystrom_le_of_eq_transpose_mul
    {Ωs : Type*} [MeasurableSpace Ωs] {ν : Measure Ωs}
    {n r k p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {F : Matrix (Fin r) (Fin n) ℝ}
    (hA : A = Fᵀ * F) (hp : 2 ≤ p) (hkn : k ≤ n)
    (Ω : Ωs → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin (k + p))) ν) :
    Integrable (fun ω => specNorm (A - nystrom A (Ω ω))) ν ∧
      ∫ ω, specNorm (A - nystrom A (Ω ω)) ∂ν ≤
        (1 + 2 * k / ((p : ℝ) - 1)) * singularValues F k ^ 2 +
          bestRankFrobSq F k * (Real.exp 1 ^ 2 * (2 * k + p) / p ^ 2) := by
  have := hΩ.isProbabilityMeasure
  obtain ⟨s, U₁, U₂, V₁, V₂, S₂, hF, hU₂, hV₁, hV₂, hV, hspec, hfrob⟩ :=
    exists_svd_right_blocks_specNorm F k hkn
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hF hV
  obtain ⟨hbi, hb⟩ := integrable_and_integral_specNorm_sq_mul_block_mul_pinvR_block_le
    Ω hΩ hV₁ hV₂ hV S₂ hp
  have hu := ae_isUnit_block hΩ V₁ hV₁ (show k ≤ k + p by omega)
  have ho := ae_hasOrthonormalCols_gaussianRangeFrame_of_hasLaw F Ω hΩ
  have hr := ae_project_gaussianRangeFrame_of_hasLaw F Ω hΩ
  have hk := ae_rank_mul_gaussian_eq_min F Ω hΩ
  have hpoint : (fun ω => specNorm (A - nystrom A (Ω ω))) ≤ᵐ[ν]
      fun ω => specNorm S₂ ^ 2 +
        specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ^ 2 := by
    filter_upwards [hu, ho, hr, hk] with ω hu ho hr hk
    rw [specNorm_sub_nystrom_eq_of_eq_transpose_mul hA,
      one_sub_mul_moorePenroseInverse_mul_eq_residual ho hr
        (by rw [hk, Fintype.card_fin]) F]
    exact specNorm_residual_sq_le_of_range_subset hF hU₂ hV₁ hV₂ hV rfl rfl hu ho hr
  have hm : AEStronglyMeasurable (fun ω => specNorm (A - nystrom A (Ω ω))) ν :=
    ((measurable_specNorm_of_entries (fun i j => measurable_const.sub
      ((Matrix.measurable_entry i j).comp (measurable_nystrom A)))).comp_aemeasurable
        hΩ.aemeasurable).aestronglyMeasurable
  have hi : Integrable (fun ω => specNorm (A - nystrom A (Ω ω))) ν :=
    ((integrable_const (specNorm S₂ ^ 2)).add hbi).mono' hm
      (hpoint.mono fun ω h => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (specNorm_nonneg _), Pi.add_apply] using h)
  refine ⟨hi, ?_⟩
  have hh := integral_mono_ae hi ((integrable_const (specNorm S₂ ^ 2)).add hbi) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hbi, integral_const, probReal_univ, one_smul] at hh
  rw [hspec, hfrob] at hb
  rw [hspec] at hh
  have hb' := hh.trans (add_le_add (le_refl (singularValues F k ^ 2)) hb)
  have heq : singularValues F k ^ 2 +
      (2 * singularValues F k ^ 2 * (k / ((p : ℝ) - 1)) +
        bestRankFrobSq F k * (Real.exp 1 ^ 2 * (2 * k + p) / p ^ 2)) =
      (1 + 2 * k / ((p : ℝ) - 1)) * singularValues F k ^ 2 +
        bestRankFrobSq F k * (Real.exp 1 ^ 2 * (2 * k + p) / p ^ 2) := by
    simp only [div_eq_mul_inv]
    ring
  exact heq ▸ hb'

/-- **Refined Gaussian Nyström spectral bound.** The next PSD eigenvalue and nuclear
spectral tail replace the singular values of a square root. Integrability and rank-deficient
inputs are included. -/
theorem integrable_and_integral_specNorm_sub_nystrom_le
    {Ωs : Type*} [MeasurableSpace Ωs] {ν : Measure Ωs}
    {n k p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (hp : 2 ≤ p) (hkn : k < n)
    (Ω : Ωs → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin (k + p))) ν) :
    Integrable (fun ω => specNorm (A - nystrom A (Ω ω))) ν ∧
      ∫ ω, specNorm (A - nystrom A (Ω ω)) ∂ν ≤
        (1 + 2 * k / ((p : ℝ) - 1)) * singularValues A k +
          nuclearNorm (A - truncatedSVD A k) *
            (Real.exp 1 ^ 2 * (2 * k + p) / p ^ 2) := by
  have hS : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hGram : (CFC.sqrt A)ᴴ * CFC.sqrt A = A := by
    rw [hS, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  have hσ : singularValues (CFC.sqrt A) k ^ 2 = singularValues A k := by
    let j : Fin (Fintype.card (Fin n)) := ⟨k, by simpa using hkn⟩
    have h := sq_singularValues_eq_eigenvalues₀ (CFC.sqrt A) j
    have he := congrFun (eigenvalues₀_eq_of_matrix_eq
      (Matrix.isHermitian_conjTranspose_mul_self (CFC.sqrt A)) hA.isHermitian hGram) j
    exact h.trans (he.trans (singularValues_eq_eigenvalues₀_of_posSemidef hA j).symm)
  have hG : A = (CFC.sqrt A)ᵀ * CFC.sqrt A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hGram.symm
  obtain ⟨hi, hb⟩ := integrable_and_integral_specNorm_sub_nystrom_le_of_eq_transpose_mul
    hG hp hkn.le Ω hΩ
  rw [hσ, bestRankFrobSq_sqrt_eq_nuclearNorm_sub_truncatedSVD hA k] at hb
  exact ⟨hi, hb⟩

end NLAlib
