/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.LowRank.Structural.RangeFinder
import NLAlib.Matrix.Spectral.SvdBlocks
import NLAlib.RandomMatrix.Gaussian.Moments.BlockDeviation
import NLAlib.RandomMatrix.Gaussian.Spectral.SketchRank

/-!
# Sharp explicit deviations for the Gaussian sampled range

Each of the Frobenius and spectral bounds has failure at most `2 t⁻ᵖ + exp (-u²/2)`.
The output is the actual projector onto the full sampled range, without a chosen random frame.
The two conclusions are individual probability statements. The improved inverse-Frobenius
tail sharpens the larger failure constants printed in HMT (2011), Theorems 10.7–10.8.
Source: the supplied randomized low-rank reroute and the native Gaussian inverse/concentration
arguments; atlas `rsvd-tail`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

private theorem measurable_rsvd_rangeResidual {m n l : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Measurable (fun G : Matrix (Fin n) (Fin l) ℝ => A - rangeProjector (A * G) * A) := by
  have hP : Measurable (fun G : Matrix (Fin n) (Fin l) ℝ => rangeProjector (A * G) * A) :=
    (measurable_rangeProjector.comp (measurable_const.matrix_mul measurable_id)).matrix_mul
      measurable_const
  refine Matrix.measurable_iff_entries.mpr fun i j => ?_
  exact measurable_const.sub ((Matrix.measurable_entry i j).comp hP)

private theorem ae_isUnit_rsvd_head
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n k p : ℕ}
    (G : Ω → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hG : HasLaw G (gaussianMatrix (Fin n) (Fin (k + p))) μ)
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : HasOrthonormalCols V) :
    ∀ᵐ ω ∂μ, IsUnit ((Vᵀ * G ω) * (Vᵀ * G ω)ᵀ) := by
  have hlaw := hasLaw_gaussianMatrix_block_of_hasLaw hG V hV
  have h := gaussianMatrix_ae_isUnit_mul_transpose (k := k) (t := k + p) (by omega)
  rw [← hlaw.map_eq] at h
  exact ae_of_ae_map hlaw.aemeasurable h

/-- The actual sampled-range Frobenius error has the improved explicit failure probability.
The target rank may be zero or exceed `rank A`; the sample width may exceed either dimension.
Source: HMT (2011), Theorem 10.7, with the proved native sharpening of its inverse tail.
Supports atlas `rsvd-tail`. -/
theorem measureReal_lt_frobNorm_rsvd_rangeResidual_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n k p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hkn : k ≤ n) (hp : 4 ≤ p)
    (G : Ω → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hG : HasLaw G (gaussianMatrix (Fin n) (Fin (k + p))) μ)
    {t u : ℝ} (ht : 1 ≤ t) (hu : 0 ≤ u) :
    μ.real {ω | (1 + t * Real.sqrt (12 * (k : ℝ) / p)) * Real.sqrt (bestRankFrobSq A k) +
        u * t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1)) * singularValues A k <
      frobNorm (A - rangeProjector (A * G ω) * A)} ≤
      2 * t ^ (-(p : ℝ)) + Real.exp (-u ^ 2 / 2) := by
  obtain ⟨r, U₁, U₂, V₁, V₂, S₂, hA, hU₂, hV₁, hV₂, hV, hspec, hfrob⟩ :=
    exists_svd_right_blocks_specNorm A k hkn
  have hFN : frobNorm S₂ = Real.sqrt (bestRankFrobSq A k) := by rw [frobNorm, hfrob]
  have hUnit := ae_isUnit_rsvd_head G hG V₁ hV₁
  have hc := gaussianMatrix_lt_frobNorm_mul_block_mul_pinvR_block_le G hG
    V₁ V₂ hV₁ hV₂ hV S₂ hp ht hu
  refine (show μ.real {ω | (1 + t * Real.sqrt (12 * (k : ℝ) / p)) *
        Real.sqrt (bestRankFrobSq A k) +
        u * t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1)) * singularValues A k <
      frobNorm (A - rangeProjector (A * G ω) * A)} ≤
      μ.real {ω | (t * Real.sqrt (12 * (k : ℝ) / p)) * frobNorm S₂ +
          u * (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * specNorm S₂ <
        frobNorm (S₂ * (V₂ᵀ * G ω) * pinvR (V₁ᵀ * G ω))} from ?_).trans hc
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  filter_upwards [hUnit] with ω hω
  change _ < frobNorm (A - rangeProjector (A * G ω) * A) → _
  intro hbad
  change (t * Real.sqrt (12 * (k : ℝ) / p)) * frobNorm S₂ +
      u * (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * specNorm S₂ <
    frobNorm (S₂ * (V₂ᵀ * G ω) * pinvR (V₁ᵀ * G ω))
  have hb := frobSq_sub_rangeProjector_mul_le_of_svd_blocks hA hU₂ hV₁ hV₂ hV
    (Ω := G ω) (Ω₁ := V₁ᵀ * G ω) (Ω₂ := V₂ᵀ * G ω) rfl rfl hω
  have hres : frobNorm (A - rangeProjector (A * G ω) * A) ≤
      frobNorm S₂ + frobNorm (S₂ * (V₂ᵀ * G ω) * pinvR (V₁ᵀ * G ω)) := by
    rw [← frobNorm_sq (A - rangeProjector (A * G ω) * A), ← frobNorm_sq S₂,
      ← frobNorm_sq (S₂ * (V₂ᵀ * G ω) * pinvR (V₁ᵀ * G ω))] at hb
    nlinarith [frobNorm_nonneg (A - rangeProjector (A * G ω) * A), frobNorm_nonneg S₂,
      frobNorm_nonneg (S₂ * (V₂ᵀ * G ω) * pinvR (V₁ᵀ * G ω))]
  rw [hFN] at hres
  rw [hFN, hspec]
  ring_nf at hbad ⊢
  linarith only [hbad, hres]

/-- The actual sampled-range spectral error has the same individual failure bound.
This does not assert both norm bounds on one event at that smaller failure probability.
Source: HMT (2011), Theorem 10.8, with the proved native inverse-Frobenius sharpening.
Supports atlas `rsvd-tail`. -/
theorem measureReal_lt_specNorm_rsvd_rangeResidual_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n k p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hkn : k ≤ n) (hp : 4 ≤ p)
    (G : Ω → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hG : HasLaw G (gaussianMatrix (Fin n) (Fin (k + p))) μ)
    {t u : ℝ} (ht : 1 ≤ t) (hu : 0 ≤ u) :
    μ.real {ω | (1 + t * Real.sqrt (12 * (k : ℝ) / p)) * singularValues A k +
        t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1)) * Real.sqrt (bestRankFrobSq A k) +
        u * t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1)) * singularValues A k <
      specNorm (A - rangeProjector (A * G ω) * A)} ≤
      2 * t ^ (-(p : ℝ)) + Real.exp (-u ^ 2 / 2) := by
  obtain ⟨r, U₁, U₂, V₁, V₂, S₂, hA, hU₂, hV₁, hV₂, hV, hspec, hfrob⟩ :=
    exists_svd_right_blocks_specNorm A k hkn
  have hFN : frobNorm S₂ = Real.sqrt (bestRankFrobSq A k) := by rw [frobNorm, hfrob]
  have hUnit := ae_isUnit_rsvd_head G hG V₁ hV₁
  have hc := gaussianMatrix_lt_specNorm_mul_block_mul_pinvR_block_le G hG
    V₁ V₂ hV₁ hV₂ hV S₂ hp ht hu
  refine (show μ.real {ω | (1 + t * Real.sqrt (12 * (k : ℝ) / p)) * singularValues A k +
        t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1)) * Real.sqrt (bestRankFrobSq A k) +
        u * t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1)) * singularValues A k <
      specNorm (A - rangeProjector (A * G ω) * A)} ≤
      μ.real {ω | (t * Real.sqrt (12 * (k : ℝ) / p)) * specNorm S₂ +
          (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * frobNorm S₂ +
          u * (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * specNorm S₂ <
        specNorm (S₂ * (V₂ᵀ * G ω) * pinvR (V₁ᵀ * G ω))} from ?_).trans hc
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  filter_upwards [hUnit] with ω hω
  change _ < specNorm (A - rangeProjector (A * G ω) * A) → _
  intro hbad
  change (t * Real.sqrt (12 * (k : ℝ) / p)) * specNorm S₂ +
      (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * frobNorm S₂ +
      u * (t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1))) * specNorm S₂ <
    specNorm (S₂ * (V₂ᵀ * G ω) * pinvR (V₁ᵀ * G ω))
  have hb := specNorm_sub_rangeProjector_mul_le_of_svd_blocks hA hU₂ hV₁ hV₂
    (Ω := G ω) (Ω₁ := V₁ᵀ * G ω) (Ω₂ := V₂ᵀ * G ω) rfl rfl hω
  rw [hspec] at hb
  rw [hFN, hspec]
  ring_nf at hbad ⊢
  linarith only [hbad, hb]

/-- A Gaussian sampled range exactly recovers every input whose rank is at most the sample
width. This includes widths beyond the ambient dimension and all empty shapes.
Source: HMT (2011), Proposition A.5; supports atlas `rsvd-tail`.
atlas: rsvd-tail (partial) -/
theorem ae_rsvd_rangeProjector_mul_eq_of_rank_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m n l : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (G : Ω → Matrix (Fin n) (Fin l) ℝ)
    (hG : HasLaw G (gaussianMatrix (Fin n) (Fin l)) μ) (hr : A.rank ≤ l) :
    ∀ᵐ ω ∂μ, rangeProjector (A * G ω) * A = A := by
  filter_upwards [ae_rank_mul_gaussian_eq_min A G hG] with ω hω
  have he : (A * G ω).rank = A.rank := by simpa only [min_eq_left hr] using hω
  exact rangeProjector_mul_of_range_le (range_mulVecLin_mul_eq_of_rank_eq A (G ω) he).symm.le

private theorem one_sub_failure_le_measureReal_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : AEMeasurable f μ) {B δ : ℝ}
    (hbad : μ.real {ω | B < f ω} ≤ δ) : 1 - δ ≤ μ.real {ω | f ω ≤ B} := by
  have hm : NullMeasurableSet {ω | f ω ≤ B} μ :=
    hf.nullMeasurableSet_preimage measurableSet_Iic
  have h := measureReal_add_measureReal_compl₀ (μ := μ) hm
  rw [probReal_univ] at h
  have he : μ.real {ω | f ω ≤ B} + μ.real {ω | B < f ω} = 1 := by
    simpa only [Set.compl_ofPred, not_le] using h
  linarith

/-- The Frobenius sampled-range guarantee with success at least
`1 - 2 t⁻ᵖ - exp (-u²/2)`, over the actual Gaussian sketch law. All singular and empty input
cases are retained; the full range output may have rank as large as the sketch width.
Source: HMT (2011), Theorem 10.7, with the native coefficient-one inverse-tail sharpening.
atlas: rsvd-tail (partial)-/
theorem measureReal_frobNorm_rsvd_rangeResidual_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n k p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hkn : k ≤ n) (hp : 4 ≤ p)
    (G : Ω → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hG : HasLaw G (gaussianMatrix (Fin n) (Fin (k + p))) μ)
    {t u : ℝ} (ht : 1 ≤ t) (hu : 0 ≤ u) :
    1 - 2 * t ^ (-(p : ℝ)) - Real.exp (-u ^ 2 / 2) ≤
      μ.real {ω | frobNorm (A - rangeProjector (A * G ω) * A) ≤
        (1 + t * Real.sqrt (12 * (k : ℝ) / p)) * Real.sqrt (bestRankFrobSq A k) +
        u * t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1)) * singularValues A k} := by
  have hm : Measurable (fun Z : Matrix (Fin n) (Fin (k + p)) ℝ =>
      frobNorm (A - rangeProjector (A * Z) * A)) :=
    Real.continuous_sqrt.measurable.comp (measurable_frobSq.comp (measurable_rsvd_rangeResidual A))
  have h := one_sub_failure_le_measureReal_le (hm.comp_aemeasurable hG.aemeasurable)
    (measureReal_lt_frobNorm_rsvd_rangeResidual_le A hkn hp G hG ht hu)
  simp only [Function.comp_apply] at h
  linarith only [h]

/-- The spectral sampled-range guarantee with the same individual success probability.
The Frobenius and spectral conclusions are separate events. Source: HMT (2011), Theorem
10.8, with the native coefficient-one inverse-Frobenius tail sharpening.
atlas: rsvd-tail (partial)-/
theorem measureReal_specNorm_rsvd_rangeResidual_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n k p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hkn : k ≤ n) (hp : 4 ≤ p)
    (G : Ω → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hG : HasLaw G (gaussianMatrix (Fin n) (Fin (k + p))) μ)
    {t u : ℝ} (ht : 1 ≤ t) (hu : 0 ≤ u) :
    1 - 2 * t ^ (-(p : ℝ)) - Real.exp (-u ^ 2 / 2) ≤
      μ.real {ω | specNorm (A - rangeProjector (A * G ω) * A) ≤
        (1 + t * Real.sqrt (12 * (k : ℝ) / p)) * singularValues A k +
        t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1)) * Real.sqrt (bestRankFrobSq A k) +
        u * t * (Real.exp 1 * Real.sqrt (k + p) / ((p : ℝ) + 1)) * singularValues A k} := by
  have hm : Measurable (fun Z : Matrix (Fin n) (Fin (k + p)) ℝ =>
      specNorm (A - rangeProjector (A * Z) * A)) :=
    measurable_specNorm_of_entries (Matrix.measurable_iff_entries.mp (measurable_rsvd_rangeResidual A))
  have h := one_sub_failure_le_measureReal_le (hm.comp_aemeasurable hG.aemeasurable)
    (measureReal_lt_specNorm_rsvd_rangeResidual_le A hkn hp G hG ht hu)
  simp only [Function.comp_apply] at h
  linarith only [h]

end NLAlib
