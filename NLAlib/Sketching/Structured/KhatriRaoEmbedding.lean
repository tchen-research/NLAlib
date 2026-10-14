import NLAlib.Sketching.Structured.KhatriRaoBasic
import NLAlib.Sketching.Properties.SubspaceEmbedding.Gram
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Probability.HasLaw

/-!
# The literal normalized Khatri–Rao embedding

The rows are independent tensor-product probes scaled by `1 / sqrt m`.
Its restricted Gram matrix is exactly the empirical covariance of the
projected probes, so the matrix covariance event is the library's usual
`IsSubspaceEmbedding` event.

Source: Heidary, *The Sharp Logarithmic Cost of Khatri–Rao Subspace
Embeddings*, equation (1.1) and Theorem 2.1.
<https://github.com/DiarHaidary/Results/blob/main/manuscripts/08-Khatri-Rao-Embeddings-and-Approximation/Khatri_Rao_Embeddings_and_Approximation_Focused.pdf>
-/

noncomputable section

open MeasureTheory Matrix

namespace NLAlib

variable {d m : ℕ} {n : Fin d → ℕ}

/-- The law of `m` independent samples of independent vector factors.
Coordinates within any individual factor may be dependent. -/
def khatriRaoSampleLaw (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ)) (m : ℕ) :
    Measure (Fin m → ∀ j : Fin d, Fin (n j) → ℝ) :=
  Measure.pi fun _ : Fin m => Measure.pi ν

/-- Independent sampling of probability factor laws is again a probability law. -/
instance khatriRaoSampleLaw_isProbabilityMeasure
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)] : IsProbabilityMeasure (khatriRaoSampleLaw ν m) := by
  unfold khatriRaoSampleLaw
  infer_instance

/-- The Khatri–Rao sketch with tensor-product rows scaled by `1 / sqrt m`.
For zero rows, the resulting matrix is the unique empty-row matrix. -/
def khatriRaoSketch (g : Fin m → ∀ j : Fin d, Fin (n j) → ℝ) :
    Matrix (Fin m) (∀ j : Fin d, Fin (n j)) ℝ :=
  (1 / Real.sqrt (m : ℝ)) • Matrix.of (fun i => khatriRaoProbe (g i))

/-- The literal normalized Khatri–Rao sketch is measurable in all its factors. -/
theorem measurable_khatriRaoSketch : Measurable (khatriRaoSketch (n := n) (m := m)) := by
  unfold khatriRaoSketch khatriRaoProbe
  fun_prop

/-- Projected tensor probes from independent factor samples have the actual
product law of their individual push-forward distributions. -/
theorem hasLaw_projected_khatriRaoProbe_samples
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)] {r : ℕ}
    (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ) :
    ProbabilityTheory.HasLaw
      (fun g : Fin m → ∀ j : Fin d, Fin (n j) → ℝ =>
        fun i => Uᵀ *ᵥ khatriRaoProbe (g i))
      (Measure.pi fun _ : Fin m =>
        (Measure.pi ν).map (fun g => Uᵀ *ᵥ khatriRaoProbe g)) (khatriRaoSampleLaw ν m) := by
  have hproj : Measurable (fun g => Uᵀ *ᵥ khatriRaoProbe g) := by
    unfold khatriRaoProbe Matrix.mulVec dotProduct
    fun_prop
  have : IsProbabilityMeasure ((Measure.pi ν).map (fun g => Uᵀ *ᵥ khatriRaoProbe g)) :=
    Measure.isProbabilityMeasure_map hproj.aemeasurable
  refine ⟨?_, ?_⟩
  · exact (measurable_pi_iff.2 fun i => hproj.comp (measurable_pi_apply i)).aemeasurable
  · exact Measure.pi_map_pi (fun _ : Fin m => hproj.aemeasurable)

/-- The projected rows of independent Khatri–Rao factor samples are independent. -/
theorem iIndepFun_projected_khatriRaoProbe_samples
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)] {r : ℕ}
    (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin m => fun g : Fin m → ∀ j : Fin d, Fin (n j) → ℝ =>
        Uᵀ *ᵥ khatriRaoProbe (g i)) (khatriRaoSampleLaw ν m) := by
  unfold khatriRaoSampleLaw
  apply ProbabilityTheory.iIndepFun_pi
    (X := fun _ : Fin m => fun g => Uᵀ *ᵥ khatriRaoProbe g)
  intro i
  apply Measurable.aemeasurable
  unfold khatriRaoProbe Matrix.mulVec dotProduct
  fun_prop

/-- Multiplying the normalized sketch by a subspace frame restricts each
tensor probe to the corresponding projected row. -/
theorem khatriRaoSketch_mul_apply {r : ℕ}
    (g : Fin m → ∀ j : Fin d, Fin (n j) → ℝ)
    (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ) (i : Fin m) (a : Fin r) :
    (khatriRaoSketch g * U) i a =
      (1 / Real.sqrt (m : ℝ)) * (Uᵀ *ᵥ khatriRaoProbe (g i)) a := by
  simp only [khatriRaoSketch, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The restricted sketch Gram matrix is the exact empirical covariance
of the projected tensor-product probes. -/
theorem transpose_khatriRaoSketch_mul_self {r : ℕ} (hm : 0 < m)
    (g : Fin m → ∀ j : Fin d, Fin (n j) → ℝ)
    (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ) :
    (khatriRaoSketch g * U)ᵀ * (khatriRaoSketch g * U) =
      (m : ℝ)⁻¹ • ∑ i : Fin m,
        Matrix.vecMulVec (Uᵀ *ᵥ khatriRaoProbe (g i)) (Uᵀ *ᵥ khatriRaoProbe (g i)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : (1 / Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ)⁻¹ := by
    rw [div_pow, Real.sq_sqrt hmpos.le]
    simp
  ext a b
  change (∑ i, (khatriRaoSketch g * U) i a * (khatriRaoSketch g * U) i b) = _
  simp only [khatriRaoSketch_mul_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (1 / Real.sqrt (m : ℝ)) ^ 2 *
        ((Uᵀ *ᵥ khatriRaoProbe (g i)) a * (Uᵀ *ᵥ khatriRaoProbe (g i)) b) := by ring
    _ = _ := by rw [hc]

/-- The restricted Gram error is the empirical average of the centered
rank-one covariance matrices of the projected probes. -/
theorem transpose_khatriRaoSketch_mul_self_sub_one {r : ℕ} (hm : 0 < m)
    (g : Fin m → ∀ j : Fin d, Fin (n j) → ℝ)
    (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ) :
    (khatriRaoSketch g * U)ᵀ * (khatriRaoSketch g * U) - 1 =
      (m : ℝ)⁻¹ • ∑ i : Fin m,
        (Matrix.vecMulVec (Uᵀ *ᵥ khatriRaoProbe (g i)) (Uᵀ *ᵥ khatriRaoProbe (g i)) - 1) := by
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  rw [transpose_khatriRaoSketch_mul_self hm, Finset.sum_sub_distrib, smul_sub]
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hmne, one_smul]

/-- The norm bound on the empirical covariance error is exactly the
subspace-embedding property of the normalized Khatri–Rao sketch. -/
theorem isSubspaceEmbedding_khatriRaoSketch_iff {r : ℕ} (hm : 0 < m)
    (g : Fin m → ∀ j : Fin d, Fin (n j) → ℝ)
    (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ)
    (hU : HasOrthonormalCols U) {ε : ℝ} (hε : 0 ≤ ε) :
    IsSubspaceEmbedding (khatriRaoSketch g) U ε ↔
      specNorm ((m : ℝ)⁻¹ • ∑ i : Fin m,
        Matrix.vecMulVec (Uᵀ *ᵥ khatriRaoProbe (g i)) (Uᵀ *ᵥ khatriRaoProbe (g i)) - 1) ≤ ε := by
  rw [isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le hU hε,
    transpose_khatriRaoSketch_mul_self hm]

/-- A uniform constant which absorbs the square-root and large-row terms
when converting a Khatri–Rao trace-moment scale to a sample budget. -/
def khatriRaoEmbeddingConstant (d : ℕ) (C : ℝ) : ℝ := 16 * (C + 1) ^ 2 * 2 ^ d

/-- The logarithmic terminal moment order used by the sharp Khatri–Rao
embedding estimate. -/
def khatriRaoMomentOrder (r : ℕ) (δ : ℝ) : ℕ := ⌈Real.log (4 * r / δ)⌉₊

/-- The dimension-to-confidence logarithm exceeds one for positive rank
and a failure probability at most one. -/
theorem one_lt_log_four_mul_rank_div {r : ℕ} (hr : 1 ≤ r)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 1 < Real.log (4 * r / δ) := by
  have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hratio : (4 : ℝ) ≤ 4 * r / δ := (le_div_iff₀ hδ).2 (by nlinarith)
  have hlog : Real.log 4 ≤ Real.log (4 * r / δ) :=
    Real.log_le_log (by norm_num) hratio
  have hf : 1 < Real.log 4 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_gt_d9]
  exact hf.trans_le hlog

/-- The chosen terminal moment order is positive and lies between the
dimension-to-confidence logarithm and twice that logarithm. -/
theorem khatriRaoMomentOrder_bounds {r : ℕ} (hr : 1 ≤ r)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ khatriRaoMomentOrder r δ ∧
      Real.log (4 * r / δ) ≤ (khatriRaoMomentOrder r δ : ℝ) ∧
      (khatriRaoMomentOrder r δ : ℝ) ≤ 2 * Real.log (4 * r / δ) := by
  have ht := one_lt_log_four_mul_rank_div hr hδ hδ1
  refine ⟨Nat.one_le_ceil_iff.2 (by linarith), Nat.le_ceil _, ?_⟩
  have hu := Nat.ceil_lt_add_one (le_of_lt (lt_trans zero_lt_one ht))
  change (⌈Real.log (4 * r / δ)⌉₊ : ℝ) ≤ _
  linarith

/-- The terminal trace-moment order makes the exponential tail smaller
than the requested failure probability, with a factor-four reserve. -/
theorem rank_mul_exp_neg_two_mul_khatriRaoMomentOrder_le
    {r : ℕ} (hr : 1 ≤ r) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (r : ℝ) * Real.exp (-2 * (khatriRaoMomentOrder r δ : ℝ)) ≤ δ / 4 := by
  have hrr : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hb := khatriRaoMomentOrder_bounds hr hδ hδ1
  have hq : (0 : ℝ) ≤ khatriRaoMomentOrder r δ := Nat.cast_nonneg _
  have he : Real.exp (-2 * (khatriRaoMomentOrder r δ : ℝ)) ≤
      Real.exp (-Real.log (4 * r / δ)) := Real.exp_le_exp.2 (by linarith [hb.2.1])
  have hratio : 0 < (4 : ℝ) * r / δ := by positivity
  rw [Real.exp_neg, Real.exp_log hratio] at he
  have hmul := mul_le_mul_of_nonneg_left he hrr.le
  have heq : (r : ℝ) * (4 * r / δ)⁻¹ = δ / 4 := by field_simp
  simpa only [heq] using hmul

/-- The sharp sample budget controls a moment error scale whenever the
chosen moment order is at most twice the logarithmic order.
Source: Heidary, Theorem 2.1, final upper-bound arithmetic. -/
theorem mul_sqrt_add_pow_div_le_of_khatriRao_budget {d : ℕ} (hd : 1 ≤ d)
    {C r m t q ε : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hm : 0 < m)
    (ht : 0 ≤ t) (hq : 0 ≤ q) (hqt : q ≤ 2 * t) (hε : 0 < ε)
    (hbudget : khatriRaoEmbeddingConstant d C *
      (r * t / ε ^ 2 + (r * t ^ (d - 1) + t ^ d) / ε) ≤ m) :
    C * (Real.sqrt (q * r / m) + q ^ (d - 1) * (r + q) / m) ≤ ε := by
  let A := khatriRaoEmbeddingConstant d C
  let L := r * t ^ (d - 1) + t ^ d
  have htwo : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hA : 0 < A := by dsimp [A, khatriRaoEmbeddingConstant]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hvar : A * (r * t / ε ^ 2) ≤ m := by
    have hpart : 0 ≤ A * (L / ε) := mul_nonneg hA.le (div_nonneg hL hε.le)
    change A * (r * t / ε ^ 2 + L / ε) ≤ m at hbudget
    nlinarith
  have hrow : A * (L / ε) ≤ m := by
    have hpart : 0 ≤ A * (r * t / ε ^ 2) := by positivity
    change A * (r * t / ε ^ 2 + L / ε) ≤ m at hbudget
    nlinarith
  have hAvar : 8 * C ^ 2 ≤ A := by
    have hsq : C ^ 2 ≤ (C + 1) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left htwo (by positivity : 0 ≤ 16 * (C + 1) ^ 2)
    dsimp [A, khatriRaoEmbeddingConstant]
    nlinarith
  have hArow : 2 * C * 2 ^ d ≤ A := by
    have hbase : 2 * C ≤ 16 * (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
    exact mul_le_mul_of_nonneg_right hbase (by positivity)
  have hvar' : A * (r * t) ≤ m * ε ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hvar (sq_nonneg ε)
    have hepsne : ε ≠ 0 := hε.ne'
    field_simp [hepsne] at hmul
    nlinarith
  have hqvar : 4 * C ^ 2 * (q * r) ≤ m * ε ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hAvar (mul_nonneg hr ht)
    have h2 := mul_le_mul_of_nonneg_right hqt (by positivity : 0 ≤ 4 * C ^ 2 * r)
    nlinarith
  have hrad : 0 ≤ q * r / m := div_nonneg (mul_nonneg hq hr) hm.le
  have hsqrt : C * Real.sqrt (q * r / m) ≤ ε / 2 := by
    have hs := Real.sq_sqrt hrad
    have hdiv : (4 * C ^ 2 * (q * r)) / m ≤ ε ^ 2 :=
      (div_le_iff₀ hm).2 (by nlinarith [hqvar])
    have heq : (4 * C ^ 2 * (q * r)) / m = 4 * C ^ 2 * (q * r / m) := by ring
    rw [heq] at hdiv
    nlinarith [Real.sqrt_nonneg (q * r / m)]
  have hqpow : q ^ (d - 1) ≤ (2 * t) ^ (d - 1) := pow_le_pow_left₀ hq hqt _
  have hqd : q ^ d ≤ (2 * t) ^ d := pow_le_pow_left₀ hq hqt _
  have htwopred : (2 : ℝ) ^ (d - 1) ≤ 2 ^ d :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 1)
  have hscale : q ^ (d - 1) * (r + q) ≤ 2 ^ d * L := by
    have hprod := mul_le_mul_of_nonneg_left hqpow hr
    have hpow : q ^ (d - 1) * q = q ^ d := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    have hpred := mul_le_mul_of_nonneg_right htwopred
      (mul_nonneg hr (pow_nonneg ht (d - 1)))
    rw [mul_pow] at hprod hqd
    dsimp [L]
    nlinarith
  have hrow' : A * L ≤ m * ε := by
    have hmul := mul_le_mul_of_nonneg_right hrow hε.le
    have hepsne : ε ≠ 0 := hε.ne'
    field_simp [hepsne] at hmul
    nlinarith
  have hlinear : C * (q ^ (d - 1) * (r + q) / m) ≤ ε / 2 := by
    have h1 := mul_le_mul_of_nonneg_right hArow hL
    have h2 := mul_le_mul_of_nonneg_left hscale hC
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hm).2
    nlinarith
  nlinarith

end NLAlib
