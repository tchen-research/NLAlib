import NLAlib.Matrix.Graph.LaplacianSum
import NLAlib.Matrix.Subspaces.OrthonormalBasisMatrix
import NLAlib.Sketching.Sampling.LeverageSamplingGram
import NLAlib.Sketching.Sampling.LeverageSampling

/-!
# Effective-resistance sampling of weighted graph edges

The probability of an original edge is its weighted effective resistance divided
by the Laplacian rank. Independent finite edge lists are accumulated into nonnegative
output weights, preserving the full-space Laplacian quadratic form. The proof frame is
an orthonormal basis of the incidence range; disconnected kernels need no special
connectedness assumption. The zero-rank branch returns zero before a sampling law is used.

Source: Spielman–Srivastava, Theorem 1 and Lemmas 3–4; Tropp 2015, matrix concentration.
Atlas: `resistance-sampling-spectral-sparsifier`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal

namespace NLAlib.GraphEdgeOrientation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : SimpleGraph V} (o : GraphEdgeOrientation G E)

/-- The actual effective-resistance probabilities, totalized outside positive rank.
Only the positive-rank theorem turns them into a probability law. -/
def resistanceSamplingProbabilities (w : E → ℝ) : E → ℝ≥0 :=
  normalizedSamplingProbabilities (fun e => w e * o.edgeResistance w e)

/-- Positive Laplacian rank makes the exact resistance probabilities sum to one.
The weights are strictly positive on the input graph; disconnected graphs are allowed. -/
theorem sum_resistanceSamplingProbabilities (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (hr : 0 < (o.laplacian w).rank) : ∑ e, o.resistanceSamplingProbabilities w e = 1 := by
  apply sum_normalizedSamplingProbabilities
  · intro e
    exact (o.weight_mul_edgeResistance_mem_Icc w (fun e => (hw e).le) e).1
  · rw [(o.sum_weight_mul_edgeResistance w hw).1]
    exact_mod_cast hr

/-- The normalized mass is literally `w_e R_e / rank L` at every edge. -/
theorem coe_resistanceSamplingProbabilities (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (hr : 0 < (o.laplacian w).rank) (e : E) :
    (o.resistanceSamplingProbabilities w e : ℝ) =
      w e * o.edgeResistance w e / (o.laplacian w).rank := by
  have ht : 0 < ∑ e, w e * o.edgeResistance w e := by
    rw [(o.sum_weight_mul_edgeResistance w hw).1]
    exact_mod_cast hr
  rw [resistanceSamplingProbabilities, coe_normalizedSamplingProbabilities _
    (fun e => (o.weight_mul_edgeResistance_mem_Icc w (fun e => (hw e).le) e).1) ht,
    (o.sum_weight_mul_edgeResistance w hw).1]

/-- Accumulate `w_e/(q p_e)` for each occurrence of the sampled edge. The zero-rank
branch returns the zero graph, without assigning a probability law to empty support. -/
def resistanceSampledWeights (w : E → ℝ) {q : ℕ} (ω : Fin q → E) : E → ℝ :=
  if (o.laplacian w).rank = 0 then fun _ => 0 else fun e =>
    w e * (sampleCount ω e : ℝ) /
      ((q : ℝ) * (o.resistanceSamplingProbabilities w e : ℝ))

/-- Every accumulated output weight is nonnegative, including zero-probability rows
and the deterministic zero-rank branch.
atlas: resistance-sampling-spectral-sparsifier (partial) -/
theorem resistanceSampledWeights_nonneg (w : E → ℝ) (hw : ∀ e, 0 ≤ w e)
    {q : ℕ} (ω : Fin q → E) (e : E) : 0 ≤ o.resistanceSampledWeights w ω e := by
  unfold resistanceSampledWeights
  split_ifs
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (hw e) (Nat.cast_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (o.resistanceSamplingProbabilities w e).coe_nonneg)

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The sampled-row Gram matrix is exactly the list sum of inverse-probability edge
Laplacians. This is an algebraic identity for the literal sampler, including zero masses. -/
theorem sampled_weightedIncidence_gram_eq_sum (w : E → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : E → ℝ≥0) {q : ℕ} (ω : Fin q → E) :
    (sampledRowMatrix (o.weightedIncidence w) p ω)ᵀ *
      sampledRowMatrix (o.weightedIncidence w) p ω =
      ∑ j, (w (ω j) / ((q : ℝ) * (p (ω j) : ℝ))) •
        Matrix.vecMulVec (o.incidence (ω j)) (o.incidence (ω j)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sampledRowMatrix, weightedIncidence,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (Real.sqrt ((q : ℝ) * (p (ω j) : ℝ)))⁻¹ ^ 2 * Real.sqrt (w (ω j)) ^ 2 *
        (o.incidence (ω j) a * o.incidence (ω j) b) := by ring
    _ = _ := by
      rw [inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (hw (ω j))]
      ring

/-- Accumulating repeated edges and retaining the sample list give exactly the same
Laplacian. Thus the probabilistic matrix guarantee applies to the returned weighted graph.
atlas: resistance-sampling-spectral-sparsifier (partial) -/
theorem laplacian_resistanceSampledWeights_eq_sampled_gram
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (hr : 0 < (o.laplacian w).rank)
    {q : ℕ} (ω : Fin q → E) :
    o.laplacian (o.resistanceSampledWeights w ω) =
      (sampledRowMatrix (o.weightedIncidence w) (o.resistanceSamplingProbabilities w) ω)ᵀ *
        sampledRowMatrix (o.weightedIncidence w) (o.resistanceSamplingProbabilities w) ω := by
  rw [o.laplacian_eq_sum_weight_smul_vecMulVec _
    (o.resistanceSampledWeights_nonneg w (fun e => (hw e).le) ω),
    o.sampled_weightedIncidence_gram_eq_sum w (fun e => (hw e).le)]
  have hf := Finset.sum_fiberwise' (Finset.univ : Finset (Fin q)) ω (fun e =>
    (w e / ((q : ℝ) * (o.resistanceSamplingProbabilities w e : ℝ))) •
      Matrix.vecMulVec (o.incidence e) (o.incidence e))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  simp only [resistanceSampledWeights, if_neg hr.ne', sampleCount]
  ring

/-- A rank-zero input returns the zero Laplacian before a sampling law is formed.
atlas: resistance-sampling-spectral-sparsifier (partial) -/
theorem laplacian_resistanceSampledWeights_eq_zero_of_rank_eq_zero
    (w : E → ℝ) (hr : (o.laplacian w).rank = 0) {q : ℕ} (ω : Fin q → E) :
    o.laplacian (o.resistanceSampledWeights w ω) = 0 := by
  simp only [resistanceSampledWeights, if_pos hr, laplacian_zero]

/-- Accumulated nonzero output edges number at most the number of draws, even when
the sample list contains repetitions.
atlas: resistance-sampling-spectral-sparsifier (partial) -/
theorem card_resistanceSampledWeights_support_le (w : E → ℝ) {q : ℕ} (ω : Fin q → E) :
    (Finset.univ.filter (fun e => o.resistanceSampledWeights w ω e ≠ 0)).card ≤ q := by
  apply (Finset.card_le_card ?_).trans (card_sampleCount_support_le ω)
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  intro hz
  apply he
  unfold resistanceSampledWeights
  split_ifs <;> simp [hz]

/-- Exact effective-resistance edge sampling preserves the full-space Laplacian
Loewner sandwich except with probability `2 r exp(-q ε²/(3 r))`, where `r = rank L`.
The output is the graph with the accumulated sample-count weights. Disconnected graphs
and isolated vertices are included, because the proof works on the full incidence range.
Source: Spielman–Srivastava, Theorem 1 and Lemmas 3–4; Tropp 2015, matrix concentration.
atlas: resistance-sampling-spectral-sparsifier (partial) -/
theorem measureReal_resistance_sampling_failure_le
    [MeasurableSpace E] [MeasurableSingletonClass E]
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (hr : 0 < (o.laplacian w).rank)
    {q : ℕ} (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (Measure.pi (fun _ : Fin q => finiteSamplingLaw (o.resistanceSamplingProbabilities w)
      (o.sum_resistanceSamplingProbabilities w hw hr))).real
      {ω | ¬ ((1 - ε) • o.laplacian w ≤ o.laplacian (o.resistanceSampledWeights w ω) ∧
        o.laplacian (o.resistanceSampledWeights w ω) ≤ (1 + ε) • o.laplacian w)} ≤
      2 * (o.laplacian w).rank *
        Real.exp (-(q : ℝ) * ε ^ 2 / (3 * (o.laplacian w).rank)) := by
  classical
  let C := o.weightedIncidence w
  let U : Matrix E (Fin C.rank) ℝ := orthonormalBasisMatrix (LinearMap.range C.mulVecLin)
  have hU : HasOrthonormalCols U := hasOrthonormalCols_orthonormalBasisMatrix _
  have hRange : LinearMap.range U.mulVecLin = LinearMap.range C.mulVecLin :=
    range_orthonormalBasisMatrix _
  have hRank : (o.laplacian w).rank = C.rank := Matrix.rank_transpose_mul_self C
  have hrC : 0 < C.rank := hRank ▸ hr
  have hUA : U * (Uᵀ * C) = C := mul_conjTranspose_mul_eq_of_range_le hU hRange.ge
  have hP : rangeProjector C = U * Uᵀ :=
    rangeProjector_eq_mul_conjTranspose_of_range_eq hU hRange.symm
  have hrow (e : E) : ∑ a, ‖U e a‖ ^ 2 = w e * o.edgeResistance w e := by
    calc
      _ = (U * Uᵀ) e e := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        apply Finset.sum_congr rfl
        intro a _
        rw [Real.norm_eq_abs, sq_abs, pow_two]
      _ = rangeProjector C e e := congrArg (fun M : Matrix E E ℝ => M e e) hP.symm
      _ = _ := (o.weight_mul_edgeResistance_eq_diag w (fun e => (hw e).le) e).symm
  have hdom (e : E) : ∑ a, ‖U e a‖ ^ 2 ≤
      (C.rank : ℝ) * (o.resistanceSamplingProbabilities w e : ℝ) := by
    rw [hrow, o.coe_resistanceSamplingProbabilities w hw hr e, hRank]
    have hrR : (0 : ℝ) < C.rank := by exact_mod_cast hrC
    exact le_of_eq (by field_simp)
  have h := measureReal_sampled_gram_sandwich_failure_le hrC hq C U hU hUA
    (o.resistanceSamplingProbabilities w) (o.sum_resistanceSamplingProbabilities w hw hr)
    hdom hε hε1
  have hEvent : {ω : Fin q → E | ¬ ((1 - ε) • o.laplacian w ≤
      o.laplacian (o.resistanceSampledWeights w ω) ∧
      o.laplacian (o.resistanceSampledWeights w ω) ≤ (1 + ε) • o.laplacian w)} =
      {ω | ¬ ((1 - ε) • (Cᵀ * C) ≤
        (sampledRowMatrix C (o.resistanceSamplingProbabilities w) ω)ᵀ *
          sampledRowMatrix C (o.resistanceSamplingProbabilities w) ω ∧
        (sampledRowMatrix C (o.resistanceSamplingProbabilities w) ω)ᵀ *
          sampledRowMatrix C (o.resistanceSamplingProbabilities w) ω ≤
            (1 + ε) • (Cᵀ * C))} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [o.laplacian_resistanceSampledWeights_eq_sampled_gram w hw hr ω]
    rfl
  rw [hEvent]
  simpa only [← hRank] using h

/-- The resistance-sampling guarantee transports to any probability space carrying
the actual independent finite edge-list law. Source: Spielman–Srivastava, Theorem 1
and Lemmas 3–4; Tropp 2015, matrix concentration. -/
theorem measureReal_resistance_sampling_failure_le_of_hasLaw
    [MeasurableSpace E] [MeasurableSingletonClass E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (hr : 0 < (o.laplacian w).rank)
    {q : ℕ} (hq : 0 < q) (X : Ω → Fin q → E)
    (hX : HasLaw X (Measure.pi (fun _ : Fin q => finiteSamplingLaw
      (o.resistanceSamplingProbabilities w) (o.sum_resistanceSamplingProbabilities w hw hr))) μ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    μ.real {ω | ¬ ((1 - ε) • o.laplacian w ≤ o.laplacian (o.resistanceSampledWeights w (X ω)) ∧
      o.laplacian (o.resistanceSampledWeights w (X ω)) ≤ (1 + ε) • o.laplacian w)} ≤
      2 * (o.laplacian w).rank *
        Real.exp (-(q : ℝ) * ε ^ 2 / (3 * (o.laplacian w).rank)) := by
  rw [hX.measureReal_eq (p := fun ω => ¬ ((1 - ε) • o.laplacian w ≤
      o.laplacian (o.resistanceSampledWeights w ω) ∧
      o.laplacian (o.resistanceSampledWeights w ω) ≤ (1 + ε) • o.laplacian w))
    (Set.toFinite _).measurableSet]
  exact o.measureReal_resistance_sampling_failure_le w hw hr hq hε hε1

/-- The explicit sample count `3 r ε⁻² log(2 r / δ)` gives failure at most `δ` for
the returned weighted graph, with the number of nonzero output edges at most `q`.
Source: Spielman–Srivastava, Theorem 1 and Lemmas 3–4; Tropp 2015, matrix concentration.
atlas: resistance-sampling-spectral-sparsifier (partial) -/
theorem measureReal_resistance_sampling_failure_le_of_sample_size
    [MeasurableSpace E] [MeasurableSingletonClass E]
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (hr : 0 < (o.laplacian w).rank)
    {q : ℕ} (hq : 0 < q) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hsize : 3 * (o.laplacian w).rank / ε ^ 2 *
      Real.log (2 * (o.laplacian w).rank / δ) ≤ q) :
    (Measure.pi (fun _ : Fin q => finiteSamplingLaw (o.resistanceSamplingProbabilities w)
      (o.sum_resistanceSamplingProbabilities w hw hr))).real
      {ω | ¬ ((1 - ε) • o.laplacian w ≤ o.laplacian (o.resistanceSampledWeights w ω) ∧
        o.laplacian (o.resistanceSampledWeights w ω) ≤ (1 + ε) • o.laplacian w)} ≤ δ := by
  apply (o.measureReal_resistance_sampling_failure_le w hw hr hq hε hε1).trans
  have hb := leverage_tail_le_of_sample_size hr (β := 1) (by norm_num) hε hδ
    (by simpa only [one_mul] using hsize)
  simpa only [neg_one_mul] using hb

end NLAlib.GraphEdgeOrientation
