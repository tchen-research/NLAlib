import NLAlib.Matrix.SvdBlocks
import NLAlib.Matrix.OptimalErrorContinuity
import NLAlib.LowRank.GaussianSketch
import NLAlib.Gaussian.SketchRank

/-!
# Standard Gaussian RSVD relative to the actual optimum

The deterministic blocks are constructed from an actual SVD and their tail is
identified with `bestRankFrobSq`, the genuine infimum over all rank-bounded
competitors. Scalar errors are proved integrable. Oversized target ranks use
Gaussian exact recovery rather than an artificial block split.

These are the standard HMT range finder and postprocessed RSVD bounds.
The proof uses the Frobenius Gaussian inverse-moment estimate.
Atlas: `rsvd-expected-error`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal BigOperators
namespace NLAlib

/-- A target rank at least the input width has zero optimal Frobenius error.
Atlas `eckart-young`, `rsvd-expected-error` (oversized-rank API). -/
theorem bestRankFrobSq_eq_zero_of_width_le {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hnk : n ≤ k) : bestRankFrobSq k A = 0 := by
  rw [bestRankFrobSq_eq_singularValueTailSq, singularValueTailSq]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : k ≤ (i : ℕ)
  · rw [if_pos hi, singularValues_eq_zero_of_width_le A (hnk.trans hi)]
    simp
  · rw [if_neg hi]

/-- A measurable supplied orthonormal frame has integrable squared projection
error, bounded by the fixed input energy. No Gaussian moment is assumed.
Atlas `rsvd-expected-error` (integrability foundation). -/
theorem integrable_frobSq_residual_of_measurable_frame
    {α Ω m n q : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [Fintype q] [DecidableEq q]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Matrix m n ℝ) (X : Ω → α) (hX : AEMeasurable X μ)
    (Qf : α → Matrix m q ℝ) (hQf : ∀ i j, Measurable fun x => Qf x i j)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Qf (X ω))) :
    Integrable (fun ω => frobSq (residual (Qf (X ω)) A)) μ := by
  refine (integrable_const (frobSq A)).mono'
    ((measurable_frobSq_residual_of A hQf).comp_aemeasurable hX).aestronglyMeasurable ?_
  filter_upwards [hQo] with ω hω
  rw [Real.norm_of_nonneg (frobSq_nonneg _)]
  exact frobSq_residual_le hω A

/-- A Gaussian sketch at least as wide as the input spans it almost surely.
Any frame projector reproducing the sketch therefore reproduces the input.
HMT 2011, Proposition A.5; atlas `rsvd-expected-error` (exact recovery). -/
theorem ae_gaussian_projection_reproduces_of_width_le
    {Ω q : Type*} [MeasurableSpace Ω] [Fintype q] [DecidableEq q]
    {μ : Measure Ω} {m n t : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (G : Ω → Matrix (Fin n) (Fin t) ℝ)
    (hG : μ.map (fun ω => Matrix.of.symm (G ω)) = gaussianMatrix n t)
    (Q : Ω → Matrix (Fin m) q ℝ)
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * G ω)) = A * G ω) (hnt : n ≤ t) :
    ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * A) = A := by
  have hunit := ae_isUnit_block hG (1 : Matrix (Fin n) (Fin n) ℝ) (by simp) hnt
  have hunit' : ∀ᵐ ω ∂μ, IsUnit (G ω * (G ω)ᵀ) := by
    simpa only [Matrix.transpose_one, Matrix.one_mul, Equiv.apply_symm_apply] using hunit
  filter_upwards [hQr, hunit'] with ω hproj hfull
  have he := congrArg (fun M : Matrix (Fin m) (Fin t) ℝ => M * pinvR (G ω)) hproj
  simpa only [Matrix.mul_assoc, mul_pinvR hfull, Matrix.mul_one] using he

/-- **Standard Gaussian RSVD projection, actual relative optimum.** For a
measurable orthonormal frame covering `range(AΩ)`, the squared error is
integrable and bounded by `(1+k/(t-k-1)) OPT_k²(A)`. Its index type is any
finite type, and all target ranks/zero shapes are included.
HMT 2011, Theorem 10.5; atlas `rsvd-expected-error`. -/
theorem integrable_and_integral_frobSq_residual_le_bestRankFrobSq_gaussian
    {Ω q : Type*} [MeasurableSpace Ω] [Fintype q] [DecidableEq q]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m n k t : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hkt : k + 2 ≤ t)
    (G : Ω → Matrix (Fin n) (Fin t) ℝ)
    (hG : μ.map (fun ω => Matrix.of.symm (G ω)) = gaussianMatrix n t)
    (Qf : (Fin n → Fin t → ℝ) → Matrix (Fin m) q ℝ)
    (hQf : ∀ i j, Measurable fun x => Qf x i j)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Qf (Matrix.of.symm (G ω))))
    (hQr : ∀ᵐ ω ∂μ, Qf (Matrix.of.symm (G ω)) *
      ((Qf (Matrix.of.symm (G ω)))ᵀ * (A * G ω)) = A * G ω) :
    Integrable (fun ω => frobSq (residual (Qf (Matrix.of.symm (G ω))) A)) μ ∧
      (∫ ω, frobSq (residual (Qf (Matrix.of.symm (G ω))) A) ∂μ) ≤
        (1 + (k : ℝ) / (t - k - 1)) * bestRankFrobSq k A := by
  have hX := aemeasurable_of_map_eq_gaussianMatrix hG
  refine ⟨integrable_frobSq_residual_of_measurable_frame A _ hX Qf hQf hQo, ?_⟩
  by_cases hkn : k ≤ n
  · obtain ⟨r, U₁, U₂, V₁, V₂, S₂, hA, hU₂, hV₁, hV₂, hV, htail⟩ :=
      exists_svd_right_blocks A k hkn
    have hb := rsvd_main_gaussian hA hU₂ hV₁ hV₂ hV hkt G hG
      (fun ω => Qf (Matrix.of.symm (G ω))) hQo hQr
    rw [htail] at hb
    exact hb
  · have hfull := ae_gaussian_projection_reproduces_of_width_le A G hG
      (fun ω => Qf (Matrix.of.symm (G ω))) hQr (by omega : n ≤ t)
    have hz : (fun ω => frobSq (residual (Qf (Matrix.of.symm (G ω))) A)) =ᵐ[μ]
        fun _ => (0 : ℝ) := by
      filter_upwards [hfull] with ω hω
      simp [residual, hω]
    rw [integral_congr_ae hz, integral_zero, bestRankFrobSq_eq_zero_of_width_le A (by omega)]
    simp

/-- Standard postprocessed rank-`k` RSVD output. The small-matrix truncated
SVD is the proved minimizer; no best-approximation predicate is assumed.
HMT 2011, §9.2; atlas `rsvd-expected-error`. -/
def truncatedRsvdOutput {m n q : ℕ} (Q : Matrix (Fin m) (Fin q) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  Q * truncatedSVD (Qᵀ * A) k

/-- Standard postprocessed RSVD has rank at most the target rank, for all
input and frame dimensions. HMT 2011, §9.2; atlas `rsvd-expected-error`. -/
theorem rank_truncatedRsvdOutput_le {m n q : ℕ} (Q : Matrix (Fin m) (Fin q) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : (truncatedRsvdOutput Q A k).rank ≤ k :=
  (Matrix.rank_mul_le_right Q (truncatedSVD (Qᵀ * A) k)).trans
    (isBestRankApprox_truncatedSVD (Qᵀ * A) k).1

/-- The scalar postprocessed error is the sum of projection error and the
actual compressed optimum. This is independent of singular-vector choices.
Atlas `rsvd-expected-error` (measurability foundation). -/
theorem frobSq_truncatedRsvdOutput_eq {m n q : ℕ}
    (Q : Matrix (Fin m) (Fin q) ℝ) (hQ : HasOrthonormalCols Q)
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    frobSq (A - truncatedRsvdOutput Q A k) =
      frobSq (residual Q A) + bestRankFrobSq k (Qᵀ * A) := by
  unfold truncatedRsvdOutput
  rw [frobSq_sub_mul_eq hQ, frobSq_sub_truncatedSVD_eq_bestRankFrobSq]

/-- Every best rank-`k` approximation of the compressed matrix has lifted
squared error at most the actual global optimum plus projection error.
HMT 2011, §9.2; atlas `truncation-lemma` (ordinary projected component).
This uses arbitrary finite indices, including empty types, and all target ranks.
The full-matrix optimum is attained by the proved Eckart–Young theorem. -/
theorem IsBestRankApprox.frobSq_sub_mul_le_bestRankFrobSq_add_frobSq_residual
    {m n q : Type*} [Fintype m] [Fintype n] [Fintype q] [DecidableEq q]
    {Q : Matrix m q ℝ} {A : Matrix m n ℝ} {Y : Matrix q n ℝ} {k : ℕ}
    (hY : IsBestRankApprox k (Qᵀ * A) Y) (hQ : HasOrthonormalCols Q) :
    frobSq (A - Q * Y) ≤ bestRankFrobSq k A + frobSq (residual Q A) := by
  obtain ⟨B, hB⟩ := exists_isBestRankApprox A k
  have hRank : (Qᵀ * B).rank ≤ k := (Matrix.rank_mul_le_right Qᵀ B).trans hB.1
  have hBest := hY.2 (Qᵀ * B) hRank
  have hContraction := frobSq_transpose_mul_le hQ (A - B)
  rw [Matrix.mul_sub, hB.frobSq_sub_eq_bestRankFrobSq] at hContraction
  rw [frobSq_sub_mul_eq hQ]
  linarith

/-- The two-residual ordinary projected-truncation bound for a compressed
Frobenius minimizer, on arbitrary finite indices. HMT 2011, §9.2;
atlas `truncation-lemma` (ordinary projected component). -/
theorem IsBestRankApprox.frobSq_sub_mul_le_bestRankFrobSq_add_two_mul_frobSq_residual
    {m n q : Type*} [Fintype m] [Fintype n] [Fintype q] [DecidableEq q]
    {Q : Matrix m q ℝ} {A : Matrix m n ℝ} {Y : Matrix q n ℝ} {k : ℕ}
    (hY : IsBestRankApprox k (Qᵀ * A) Y) (hQ : HasOrthonormalCols Q) :
    frobSq (A - Q * Y) ≤ bestRankFrobSq k A + 2 * frobSq (residual Q A) := by
  have h := hY.frobSq_sub_mul_le_bestRankFrobSq_add_frobSq_residual hQ
  linarith [frobSq_nonneg (residual Q A)]

/-- Ordinary projected truncation has squared Frobenius error at most the
actual rank-`k` optimum plus squared projection error. The small truncated SVD
is the proved minimizer, so no best-approximation certificate is assumed.
HMT 2011, §9.2; atlas `truncation-lemma` (ordinary projected component).
Frobenius contraction gives coefficient `1` on the projection error. -/
theorem frobSq_sub_truncatedRsvdOutput_le_bestRankFrobSq_add_frobSq_residual
    {m n q : ℕ} (Q : Matrix (Fin m) (Fin q) ℝ) (hQ : HasOrthonormalCols Q)
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    frobSq (A - truncatedRsvdOutput Q A k) ≤
      bestRankFrobSq k A + frobSq (residual Q A) := by
  have hY := isBestRankApprox_truncatedSVD (Qᵀ * A) k
  exact hY.frobSq_sub_mul_le_bestRankFrobSq_add_frobSq_residual hQ

/-- The standard two-residual ordinary projected-truncation bound for the
literal truncated-SVD output. HMT 2011, §9.2; atlas `truncation-lemma`
(ordinary projected component). This follows from the stronger coefficient-one
bound and includes all target ranks and empty shapes. -/
theorem frobSq_sub_truncatedRsvdOutput_le_bestRankFrobSq_add_two_mul_frobSq_residual
    {m n q : ℕ} (Q : Matrix (Fin m) (Fin q) ℝ) (hQ : HasOrthonormalCols Q)
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    frobSq (A - truncatedRsvdOutput Q A k) ≤
      bestRankFrobSq k A + 2 * frobSq (residual Q A) := by
  have h := frobSq_sub_truncatedRsvdOutput_le_bestRankFrobSq_add_frobSq_residual Q hQ A k
  linarith [frobSq_nonneg (residual Q A)]

/-- Actual postprocessed RSVD has integrable scalar squared error. This uses
continuity of the optimum, not a measurability assumption on an arbitrary
classical SVD selector. Atlas `rsvd-expected-error`. -/
theorem integrable_frobSq_truncatedRsvdOutput_of_measurable_frame
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m n q : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) (X : Ω → α) (hX : AEMeasurable X μ)
    (Qf : α → Matrix (Fin m) (Fin q) ℝ) (hQf : ∀ i j, Measurable fun x => Qf x i j)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Qf (X ω))) :
    Integrable (fun ω => frobSq (A - truncatedRsvdOutput (Qf (X ω)) A k)) μ := by
  have hCompressed : Measurable fun x => Matrix.of.symm ((Qf x)ᵀ * A) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact measurable_mul_entry_of (f := fun x => (Qf x)ᵀ) (g := fun _ : α => A)
      (fun a b => hQf b a) (fun _ _ => measurable_const) i j
  have hOpt : Measurable fun x => bestRankFrobSq k ((Qf x)ᵀ * A) :=
    (measurable_bestRankFrobSq k).comp hCompressed
  have hValue := (measurable_frobSq_residual_of A hQf).add hOpt
  have hEq : (fun ω => frobSq (A - truncatedRsvdOutput (Qf (X ω)) A k)) =ᵐ[μ]
      fun ω => frobSq (residual (Qf (X ω)) A) + bestRankFrobSq k ((Qf (X ω))ᵀ * A) := by
    filter_upwards [hQo] with ω hω
    exact frobSq_truncatedRsvdOutput_eq _ hω A k
  have hMeas := (hValue.comp_aemeasurable hX).aestronglyMeasurable.congr hEq.symm
  refine (integrable_const (frobSq A)).mono' hMeas ?_
  filter_upwards [hQo] with ω hω
  rw [Real.norm_of_nonneg (frobSq_nonneg _)]
  have hbest := (isBestRankApprox_truncatedSVD ((Qf (X ω))ᵀ * A) k).2
    (0 : Matrix (Fin q) (Fin n) ℝ) (by simp)
  rw [sub_zero] at hbest
  have hpyth := frobSq_eq_frobSq_transpose_mul_add_residual hω A
  rw [truncatedRsvdOutput, frobSq_sub_mul_eq hω]
  linarith

/-- **Standard rank-`k` postprocessed Gaussian RSVD, actual relative optimum.**
The constructed small truncated SVD gives integrable error and the HMT
`(1+k/(t-k-1)) OPT_k²(A)` bound for every target rank and zero shape.
HMT 2011, Theorem 10.5; atlas `rsvd-expected-error`. -/
theorem integrable_and_integral_frobSq_truncatedRsvdOutput_le_bestRankFrobSq_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n q k t : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hkt : k + 2 ≤ t)
    (G : Ω → Matrix (Fin n) (Fin t) ℝ)
    (hG : μ.map (fun ω => Matrix.of.symm (G ω)) = gaussianMatrix n t)
    (Qf : (Fin n → Fin t → ℝ) → Matrix (Fin m) (Fin q) ℝ)
    (hQf : ∀ i j, Measurable fun x => Qf x i j)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Qf (Matrix.of.symm (G ω))))
    (hQr : ∀ᵐ ω ∂μ, Qf (Matrix.of.symm (G ω)) *
      ((Qf (Matrix.of.symm (G ω)))ᵀ * (A * G ω)) = A * G ω) :
    Integrable (fun ω => frobSq (A - truncatedRsvdOutput (Qf (Matrix.of.symm (G ω))) A k)) μ ∧
      (∫ ω, frobSq (A - truncatedRsvdOutput (Qf (Matrix.of.symm (G ω))) A k) ∂μ) ≤
        (1 + (k : ℝ) / (t - k - 1)) * bestRankFrobSq k A := by
  have hX := aemeasurable_of_map_eq_gaussianMatrix hG
  refine ⟨integrable_frobSq_truncatedRsvdOutput_of_measurable_frame A k _ hX Qf hQf hQo, ?_⟩
  by_cases hkn : k ≤ n
  · obtain ⟨r, U₁, U₂, V₁, V₂, S₂, hA, hU₂, hV₁, hV₂, hV, htail⟩ :=
      exists_svd_right_blocks A k hkn
    have hb := rsvd_truncated_main_gaussian hA hU₂ hV₁ hV₂ hV hkt G hG
      (fun ω => Qf (Matrix.of.symm (G ω)))
      (fun ω => truncatedSVD ((Qf (Matrix.of.symm (G ω)))ᵀ * A) k)
      hQo hQr (fun _ => isBestRankApprox_truncatedSVD _ k)
    rw [htail] at hb
    exact hb
  · have hfull := ae_gaussian_projection_reproduces_of_width_le A G hG
      (fun ω => Qf (Matrix.of.symm (G ω))) hQr (by omega : n ≤ t)
    have hOpt : bestRankFrobSq k A = 0 := bestRankFrobSq_eq_zero_of_width_le A (by omega)
    have hcompressed (ω : Ω) : bestRankFrobSq k ((Qf (Matrix.of.symm (G ω)))ᵀ * A) = 0 :=
      bestRankFrobSq_eq_zero_of_width_le _ (by omega)
    have hz : (fun ω => frobSq (A - truncatedRsvdOutput (Qf (Matrix.of.symm (G ω))) A k)) =ᵐ[μ]
        fun _ => (0 : ℝ) := by
      filter_upwards [hfull, hQo] with ω hω horth
      rw [frobSq_truncatedRsvdOutput_eq _ horth, hcompressed]
      simp [residual, hω]
    rw [integral_congr_ae hz, integral_zero, hOpt]
    simp

/-- **Constructed Gaussian range finder, actual relative optimum.** The
entrywise measurable exact-range frame has `min(rank A,t)` columns and is
constructed from the Gaussian sketch, so no frame, rank or moment certificates
are assumed. Its squared projection error is integrable and satisfies the HMT
`(1+k/(t-k-1)) OPT_k²(A)` bound. Every target rank and empty shape is covered.
HMT 2011, Theorem 10.5; atlas `rsvd-expected-error`. -/
theorem integrable_and_integral_frobSq_residual_gaussianRangeFrame_le_bestRankFrobSq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n k t : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hkt : k + 2 ≤ t)
    (G : Ω → Matrix (Fin n) (Fin t) ℝ)
    (hG : μ.map (fun ω => Matrix.of.symm (G ω)) = gaussianMatrix n t) :
    Integrable (fun ω => frobSq (residual (gaussianRangeFrame A t (Matrix.of.symm (G ω))) A)) μ ∧
      (∫ ω, frobSq (residual (gaussianRangeFrame A t (Matrix.of.symm (G ω))) A) ∂μ) ≤
        (1 + (k : ℝ) / (t - k - 1)) * bestRankFrobSq k A := by
  exact integrable_and_integral_frobSq_residual_le_bestRankFrobSq_gaussian A hkt G hG
    (gaussianRangeFrame A t) (measurable_gaussianRangeFrame_entry A t)
    (ae_hasOrthonormalCols_gaussianRangeFrame_of_map_eq A (fun ω => Matrix.of.symm (G ω)) hG)
    (by simpa only [Equiv.apply_symm_apply] using
      ae_project_gaussianRangeFrame_of_map_eq A (fun ω => Matrix.of.symm (G ω)) hG)

/-- **Constructed rank-`k` Gaussian RSVD, actual relative optimum.** The
exact Gaussian range frame followed by the proved truncated-SVD minimizer
needs no supplied frame or best-approximation certificate. The actual scalar
squared output error is integrable and satisfies the same HMT relative bound,
including zero rank and oversized target ranks. The output has rank at most
`k` by `rank_truncatedRsvdOutput_le`.
HMT 2011, Theorem 10.5 and §9.2; atlas `rsvd-expected-error`. -/
theorem integrable_and_integral_frobSq_truncatedRsvdOutput_gaussianRangeFrame_le_bestRankFrobSq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n k t : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hkt : k + 2 ≤ t)
    (G : Ω → Matrix (Fin n) (Fin t) ℝ)
    (hG : μ.map (fun ω => Matrix.of.symm (G ω)) = gaussianMatrix n t) :
    Integrable (fun ω => frobSq
      (A - truncatedRsvdOutput (gaussianRangeFrame A t (Matrix.of.symm (G ω))) A k)) μ ∧
      (∫ ω, frobSq
        (A - truncatedRsvdOutput (gaussianRangeFrame A t (Matrix.of.symm (G ω))) A k) ∂μ) ≤
        (1 + (k : ℝ) / (t - k - 1)) * bestRankFrobSq k A := by
  exact integrable_and_integral_frobSq_truncatedRsvdOutput_le_bestRankFrobSq_gaussian
    A hkt G hG (gaussianRangeFrame A t) (measurable_gaussianRangeFrame_entry A t)
    (ae_hasOrthonormalCols_gaussianRangeFrame_of_map_eq A (fun ω => Matrix.of.symm (G ω)) hG)
    (by simpa only [Equiv.apply_symm_apply] using
      ae_project_gaussianRangeFrame_of_map_eq A (fun ω => Matrix.of.symm (G ω)) hG)

end NLAlib
