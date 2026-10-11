import NLAlib.Concentration.Matrix.SamplingWithoutReplacement
import NLAlib.Concentration.Matrix.SamplingSpectralBounds

/-!
# Genuine without-replacement Chernoff endpoints

The actual subset law satisfies both matrix Chernoff tails after the proved
convex-order trace MGF comparison. Source: `sh:srht-ose`; atlas `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory
open scoped Classical Matrix Matrix.Norms.L2Operator ENNReal ComplexOrder
namespace NLAlib

/-- The actual distinct-row population sum satisfies the independent-sum
trace MGF bound, using the proved coupling rather than independence of its
selected rows. Source: `sh:convex-sampling` and `sh:srht-ose`. -/
theorem integral_traceExp_uniform_subset_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {d k : ℕ} [NeZero d]
    (hk0 : 0 < k) (hk : k ≤ Fintype.card α)
    (A : α → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hA : ∀ j, (A j).IsHermitian)
    (hbound : ∀ j, 0 ≤ lambdaMin (A j) ∧ lambdaMax (A j) ≤ L)
    (hmean : (1 / (Fintype.card α : ℝ)) • ∑ j, A j = 1) (θ : ℝ) :
    (∫ T, traceExp (θ • ∑ j ∈ T.val, A j) ∂(uniformExactRowSubsetPMF hk).toMeasure) ≤
      d * Real.exp ((k : ℝ) * chernoffCgfCoefficient L θ) :=
  (integral_traceExp_uniform_subset_le_iid hk0 hk A hA θ).trans
    (integral_traceExp_uniform_iid_le A L hL hA hbound hmean θ)

/-- The upper tail for the actual uniform distinct-row mean.
Source: `sh:srht-ose`, with the exact Chernoff coefficient `3`. -/
theorem matrix_chernoff_uniform_subset_upper
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {d k : ℕ} [NeZero d]
    (hk0 : 0 < k) (hk : k ≤ Fintype.card α)
    (A : α → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hA : ∀ j, (A j).IsHermitian)
    (hbound : ∀ j, 0 ≤ lambdaMin (A j) ∧ lambdaMax (A j) ≤ L)
    (hmean : (1 / (Fintype.card α : ℝ)) • ∑ j, A j = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((uniformExactRowSubsetPMF hk).toMeasure
      {T | 1 + ε ≤ lambdaMax ((1 / (k : ℝ)) • ∑ j ∈ T.val, A j)}).toReal ≤
      d * Real.exp (-(ε ^ 2) * k / (3 * L)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hc : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  let μ := (uniformExactRowSubsetPMF hk).toMeasure
  let Y : ExactRowSubset α k → Matrix (Fin d) (Fin d) ℂ := fun T => ∑ j ∈ T.val, A j
  let θ := Real.log (1 + ε) / L
  have hθ : 0 < θ := div_pos (Real.log_pos (by linarith)) hL
  have hset : {T | 1 + ε ≤ lambdaMax ((1 / (k : ℝ)) • Y T)} =
      {T | (1 + ε) * k ≤ lambdaMax (Y T)} := by
    ext T
    simp only [Set.mem_ofPred_eq, lambdaMax_smul_of_pos _ hc,
      one_div_mul_eq_div, le_div_iff₀ hkR]
  change (μ {T | 1 + ε ≤ lambdaMax ((1 / (k : ℝ)) • Y T)}).toReal ≤ _
  rw [hset]
  have hlap := (measure_lambdaMax_ge_le_and_measure_lambdaMin_le_le μ Y θ
    Measurable.of_discrete (Filter.Eventually.of_forall (fun T =>
      isSelfAdjoint_sum _ (fun j _ => hA j))) Integrable.of_finite).1 hθ ((1 + ε) * k)
  have htr := integral_traceExp_uniform_subset_le hk0 hk A L hL.le hA hbound hmean θ
  have hg : chernoffCgfCoefficient L θ = ε / L := by
    rw [chernoffCgfCoefficient, if_neg hL.ne']
    dsimp only [θ]
    rw [div_mul_cancel₀ _ hL.ne', Real.exp_log (by linarith : 0 < 1 + ε)]
    congr 1
    ring
  calc
    _ ≤ Real.exp (-θ * ((1 + ε) * k)) *
        (d * Real.exp ((k : ℝ) * chernoffCgfCoefficient L θ)) :=
      hlap.trans (mul_le_mul_of_nonneg_left htr (Real.exp_pos _).le)
    _ = d * Real.exp (((k : ℝ) / L) * (ε - (1 + ε) * Real.log (1 + ε))) := by
      rw [hg]
      rw [show Real.exp (-θ * ((1 + ε) * k)) * (d * Real.exp ((k : ℝ) * (ε / L))) =
        d * (Real.exp (-θ * ((1 + ε) * k)) * Real.exp ((k : ℝ) * (ε / L))) by ring,
        ← Real.exp_add]
      congr 2
      dsimp only [θ]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (sub_mul_log_one_add_le hε.le hε1)
        (show 0 ≤ (k : ℝ) / L by positivity)
      calc
        _ ≤ ((k : ℝ) / L) * -(ε ^ 2 / 3) := hh
        _ = _ := by ring

/-- The lower tail for the actual uniform distinct-row mean.
Source: `sh:srht-ose`, with the exact Chernoff coefficient `2`. -/
theorem matrix_chernoff_uniform_subset_lower
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {d k : ℕ} [NeZero d]
    (hk0 : 0 < k) (hk : k ≤ Fintype.card α)
    (A : α → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hA : ∀ j, (A j).IsHermitian)
    (hbound : ∀ j, 0 ≤ lambdaMin (A j) ∧ lambdaMax (A j) ≤ L)
    (hmean : (1 / (Fintype.card α : ℝ)) • ∑ j, A j = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ((uniformExactRowSubsetPMF hk).toMeasure
      {T | lambdaMin ((1 / (k : ℝ)) • ∑ j ∈ T.val, A j) ≤ 1 - ε}).toReal ≤
      d * Real.exp (-(ε ^ 2) * k / (2 * L)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hc : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  let μ := (uniformExactRowSubsetPMF hk).toMeasure
  let Y : ExactRowSubset α k → Matrix (Fin d) (Fin d) ℂ := fun T => ∑ j ∈ T.val, A j
  let θ := Real.log (1 - ε) / L
  have hθ : θ < 0 := div_neg_of_neg_of_pos
    (Real.log_neg (by linarith) (by linarith)) hL
  have hset : {T | lambdaMin ((1 / (k : ℝ)) • Y T) ≤ 1 - ε} =
      {T | lambdaMin (Y T) ≤ (1 - ε) * k} := by
    ext T
    simp only [Set.mem_ofPred_eq, lambdaMin_smul_of_pos _ hc,
      one_div_mul_eq_div, div_le_iff₀ hkR]
  change (μ {T | lambdaMin ((1 / (k : ℝ)) • Y T) ≤ 1 - ε}).toReal ≤ _
  rw [hset]
  have hlap := (measure_lambdaMax_ge_le_and_measure_lambdaMin_le_le μ Y θ
    Measurable.of_discrete (Filter.Eventually.of_forall (fun T =>
      isSelfAdjoint_sum _ (fun j _ => hA j))) Integrable.of_finite).2 hθ ((1 - ε) * k)
  have htr := integral_traceExp_uniform_subset_le hk0 hk A L hL.le hA hbound hmean θ
  have hg : chernoffCgfCoefficient L θ = -ε / L := by
    rw [chernoffCgfCoefficient, if_neg hL.ne']
    dsimp only [θ]
    rw [div_mul_cancel₀ _ hL.ne', Real.exp_log (by linarith : 0 < 1 - ε)]
    congr 1
    ring
  calc
    _ ≤ Real.exp (-θ * ((1 - ε) * k)) *
        (d * Real.exp ((k : ℝ) * chernoffCgfCoefficient L θ)) :=
      hlap.trans (mul_le_mul_of_nonneg_left htr (Real.exp_pos _).le)
    _ = d * Real.exp (((k : ℝ) / L) * (-ε - (1 - ε) * Real.log (1 - ε))) := by
      rw [hg]
      rw [show Real.exp (-θ * ((1 - ε) * k)) * (d * Real.exp ((k : ℝ) * (-ε / L))) =
        d * (Real.exp (-θ * ((1 - ε) * k)) * Real.exp ((k : ℝ) * (-ε / L))) by ring,
        ← Real.exp_add]
      congr 2
      dsimp only [θ]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (neg_sub_mul_log_one_sub_le hε.le hε1)
        (show 0 ≤ (k : ℝ) / L by positivity)
      calc
        _ ≤ ((k : ℝ) / L) * -(ε ^ 2 / 2) := hh
        _ = _ := by ring

/-- The genuine uniform distinct-row empirical mean satisfies the two-sided
operator norm Chernoff bound. Source: `sh:srht-ose`, with constant `3`. -/
theorem measure_spectralNorm_uniform_subset_sub_one_le
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {d k : ℕ} [NeZero d]
    (hk0 : 0 < k) (hk : k ≤ Fintype.card α)
    (A : α → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 < L)
    (hA : ∀ j, (A j).IsHermitian)
    (hbound : ∀ j, 0 ≤ lambdaMin (A j) ∧ lambdaMax (A j) ≤ L)
    (hmean : (1 / (Fintype.card α : ℝ)) • ∑ j, A j = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ((uniformExactRowSubsetPMF hk).toMeasure
      {T | ε ≤ spectralNorm ((1 / (k : ℝ)) • ∑ j ∈ T.val, A j - 1)}).toReal ≤
      2 * d * Real.exp (-(ε ^ 2) * k / (3 * L)) := by
  let Y : ExactRowSubset α k → Matrix (Fin d) (Fin d) ℂ :=
    fun T => (1 / (k : ℝ)) • ∑ j ∈ T.val, A j
  let μ := (uniformExactRowSubsetPMF hk).toMeasure
  have hsub : {T | ε ≤ spectralNorm (Y T - 1)} ⊆
      {T | lambdaMin (Y T) ≤ 1 - ε} ∪ {T | 1 + ε ≤ lambdaMax (Y T)} := by
    intro T hT
    have hsum : (∑ j ∈ T.val, A j).IsHermitian :=
      isSelfAdjoint_sum _ (fun j _ => hA j)
    have hYT : (Y T).IsHermitian := hsum.smul (IsSelfAdjoint.all (1 / (k : ℝ)))
    exact lambdaMin_le_or_le_lambdaMax_of_le_spectralNorm_sub_one hYT hT
  have hl := matrix_chernoff_uniform_subset_lower hk0 hk A L hL hA hbound hmean hε hε1
  have hu := matrix_chernoff_uniform_subset_upper hk0 hk A L hL hA hbound hmean hε hε1.le
  have he : d * Real.exp (-(ε ^ 2) * k / (2 * L)) ≤
      d * Real.exp (-(ε ^ 2) * k / (3 * L)) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ ε ^ 2 * (k : ℝ) := by positivity
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * L) (by positivity : 0 < 3 * L)]
    nlinarith
  calc
    _ ≤ (μ ({T | lambdaMin (Y T) ≤ 1 - ε} ∪ {T | 1 + ε ≤ lambdaMax (Y T)})).toReal :=
      measureReal_mono hsub
    _ ≤ (μ {T | lambdaMin (Y T) ≤ 1 - ε}).toReal +
        (μ {T | 1 + ε ≤ lambdaMax (Y T)}).toReal := measureReal_union_le _ _
    _ ≤ d * Real.exp (-(ε ^ 2) * k / (2 * L)) +
        d * Real.exp (-(ε ^ 2) * k / (3 * L)) := add_le_add hl hu
    _ ≤ _ := by linarith

end NLAlib
