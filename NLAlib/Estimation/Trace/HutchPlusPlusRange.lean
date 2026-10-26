import NLAlib.Estimation.Trace.HutchPlusPlus
import NLAlib.Matrix.Norms.NuclearTail
import NLAlib.LowRank.Nystrom.Structural
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Gaussian range error for Hutch++

The canonical range projector inherits the expected Frobenius error of the constructed
Gaussian range frame. A block of `2k+1` Gaussian columns has failure at most `1/4` at
threshold `8 tr(A)^2/k`. Source: HMT 2011, Theorem 10.5; Meyer et al. 2021,
and the block amplification route in the supplied estimation derivations, §1.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The actual canonical Gaussian range residual has the HMT expected Frobenius bound,
including rank deficiency, oversized ranks and empty shapes. -/
theorem integrable_and_integral_frobSq_sub_rangeProjector_mul_le
    {m n k t : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hkt : k + 2 ≤ t)
    {G : Ω → Matrix (Fin n) (Fin t) ℝ}
    (hG : HasLaw G (gaussianMatrix (Fin n) (Fin t)) μ) :
    Integrable (fun ω => frobSq ((1 - rangeProjector (A * G ω)) * A)) μ ∧
      (∫ ω, frobSq ((1 - rangeProjector (A * G ω)) * A) ∂μ) ≤
        (1 + (k : ℝ) / (t - k - 1)) * bestRankFrobSq A k := by
  let : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  obtain ⟨hi, he⟩ :=
    integrable_and_integral_frobSq_residual_gaussianRangeFrame_le_bestRankFrobSq A hkt G hG
  have hae : (fun ω => frobSq (projResidual (gaussianRangeFrame A t (G ω)) A)) =ᵐ[μ]
      fun ω => frobSq ((1 - rangeProjector (A * G ω)) * A) := by
    filter_upwards [ae_hasOrthonormalCols_gaussianRangeFrame_of_hasLaw A G hG,
      ae_project_gaussianRangeFrame_of_hasLaw A G hG,
      ae_rank_mul_gaussian_eq_min A G hG] with ω ho hp hr
    rw [rangeProjector_eq_mul_moorePenroseInverse,
      one_sub_mul_moorePenroseInverse_mul_eq_residual ho hp (by rw [hr, Fintype.card_fin]) A]
  exact ⟨hi.congr hae, (integral_congr_ae hae).symm.le.trans he⟩

/-- One Gaussian range block has failure at most a quarter for the trace-scaled residual.
Zero trace is handled by the vanishing expected nonnegative error. -/
theorem measureReal_frobSq_sub_rangeProjector_mul_gt_le_quarter
    {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hk : 0 < k)
    {G : Ω → Matrix (Fin n) (Fin (2 * k + 1)) ℝ}
    (hG : HasLaw G (gaussianMatrix (Fin n) (Fin (2 * k + 1))) μ) :
    μ.real {ω | 8 * A.trace ^ 2 / k < frobSq ((1 - rangeProjector (A * G ω)) * A)} ≤
      (1 / 4 : ℝ) := by
  let : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  obtain ⟨hi, he⟩ := integrable_and_integral_frobSq_sub_rangeProjector_mul_le
    (k := k) A (by omega) hG
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : 0 ≤ A.trace ^ 2 / k := by positivity
  have he' : (∫ ω, frobSq ((1 - rangeProjector (A * G ω)) * A) ∂μ) ≤
      2 * (A.trace ^ 2 / k) := by
    have hcoeff : 1 + (k : ℝ) / ((2 * k + 1 : ℕ) - k - 1) = 2 := by
      push_cast
      have hden : (2 * (k : ℝ) + 1 - k - 1) = k := by ring
      rw [hden, div_self hkR.ne']
      norm_num
    rw [hcoeff] at he
    exact he.trans (mul_le_mul_of_nonneg_left (bestRankFrobSq_le_trace_sq_div hA hk) (by norm_num))
  by_cases hc0 : A.trace ^ 2 / k = 0
  · have he0 : (∫ ω, frobSq ((1 - rangeProjector (A * G ω)) * A) ∂μ) = 0 := by
      rw [hc0, mul_zero] at he'
      exact le_antisymm he' (integral_nonneg fun _ => frobSq_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg (fun ω => frobSq_nonneg _) hi).1 he0
    have hz : μ {ω | 8 * A.trace ^ 2 / k < frobSq ((1 - rangeProjector (A * G ω)) * A)} = 0 := by
      apply measure_mono_null (t := {ω | frobSq ((1 - rangeProjector (A * G ω)) * A) ≠ 0})
        _ (ae_iff.mp hae)
      intro ω hω
      have hh : 8 * A.trace ^ 2 / k = 0 := by rw [mul_div_assoc, hc0, mul_zero]
      simp only [Set.mem_ofPred_eq, hh] at hω ⊢
      exact ne_of_gt hω
    simp [measureReal_def, hz]
  · have hcp : 0 < A.trace ^ 2 / k := lt_of_le_of_ne hc (Ne.symm hc0)
    have hm := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => frobSq_nonneg ((1 - rangeProjector (A * G ω)) * A))
      hi (8 * A.trace ^ 2 / k)
    apply (measureReal_mono (show
      {ω | 8 * A.trace ^ 2 / k < frobSq ((1 - rangeProjector (A * G ω)) * A)} ⊆
      {ω | 8 * A.trace ^ 2 / k ≤ frobSq ((1 - rangeProjector (A * G ω)) * A)} from
      fun ω h => show 8 * A.trace ^ 2 / k ≤ _ from le_of_lt h)).trans
    rw [mul_div_assoc] at hm ⊢
    have hpos : 0 < 8 * (A.trace ^ 2 / k) := by positivity
    nlinarith

/-- Compressing the range residual on the right cannot increase its squared Frobenius norm. -/
theorem frobSq_hutchPlusPlusResidual_le {n s : Type*} [Fintype n] [Fintype s]
    [DecidableEq n] (A : Matrix n n ℝ) (S : Matrix n s ℝ) :
    frobSq (hutchPlusPlusResidual A S) ≤ frobSq ((1 - rangeProjector (A * S)) * A) := by
  have h := frobSq_mul_le_frobSq_mul_specNorm_sq
    ((1 - rangeProjector (A * S)) * A) (1 - rangeProjector (A * S))
  have hp := specNorm_one_sub_rangeProjector_le_one (A * S)
  have hn := specNorm_nonneg (1 - rangeProjector (A * S))
  have hs : specNorm (1 - rangeProjector (A * S)) ^ 2 ≤ 1 := by nlinarith
  exact h.trans (by nlinarith [frobSq_nonneg ((1 - rangeProjector (A * S)) * A)])

end NLAlib
