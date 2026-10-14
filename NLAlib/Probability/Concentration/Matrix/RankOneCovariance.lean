import NLAlib.ForMathlib.Analysis.FiniteMomentRecurrence
import NLAlib.ForMathlib.MeasureTheory.PolynomialIntegrability
import NLAlib.ForMathlib.MeasureTheory.SqrtIntegral
import NLAlib.Matrix.Functions.HermitianMoments
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite-moment concentration for iid rank-one covariance sums

The genuine finite product law for iid vector samples is connected to the scalar factorial
moment recurrence. Polynomial integrability is derived from finite norm moments of one sample.
Source: Khatri–Rao embedding manuscript, Appendix `closed:thm:moment`.
-/

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}

/-- The centered rank-one covariance matrix of a vector sample. -/
def centeredRankOneCovariance (y : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  vecMulVec y y - 1

/-- The centered covariance sum over a finite tuple of iid vector samples. -/
def rankOneCovarianceSum (y : Ω → Fin r → ℝ) {n : ℕ} (ω : Fin n → Ω) :
    Matrix (Fin r) (Fin r) ℝ :=
  ∑ i, centeredRankOneCovariance (y (ω i))

/-- The normalized even trace moment of the centered iid covariance sum. -/
def rankOneCovarianceMoment (y : Ω → Fin r → ℝ) (μ : Measure Ω) (n p : ℕ) : ℝ :=
  (∫ ω : Fin n → Ω, (rankOneCovarianceSum y ω ^ (2 * p)).trace
    ∂Measure.pi fun _ : Fin n => μ) / r

/-- A centered rank-one covariance matrix is real symmetric. -/
theorem isHermitian_centeredRankOneCovariance (y : Fin r → ℝ) :
    (centeredRankOneCovariance y).IsHermitian := by
  unfold centeredRankOneCovariance
  apply Matrix.IsHermitian.ext
  intro i j
  simp [vecMulVec_apply, Matrix.one_apply, mul_comm, eq_comm]

omit [MeasurableSpace Ω] in
/-- Every centered covariance sum is real symmetric. -/
theorem isHermitian_rankOneCovarianceSum (y : Ω → Fin r → ℝ) {n : ℕ} (ω : Fin n → Ω) :
    (rankOneCovarianceSum y ω).IsHermitian := by
  unfold rankOneCovarianceSum
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [Matrix.sum_apply]
  exact Finset.sum_congr rfl fun a _ => (isHermitian_centeredRankOneCovariance (y (ω a))).apply i j

omit [MeasurableSpace Ω] in
/-- Prepending one sample adds its centered covariance matrix to the sum. -/
theorem rankOneCovarianceSum_cons (y : Ω → Fin r → ℝ) {n : ℕ} (ω : Fin n → Ω) (v : Ω) :
    rankOneCovarianceSum y (Fin.cons v ω) =
      rankOneCovarianceSum y ω + centeredRankOneCovariance (y v) := by
  simp [rankOneCovarianceSum, Fin.sum_univ_succ, add_comm]

private theorem measurePreserving_sampleCons (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun z : Ω × (Fin n → Ω) => Fin.cons z.1 z.2)
      (μ.prod (Measure.pi fun _ : Fin n => μ)) (Measure.pi fun _ : Fin (n + 1) => μ) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  have he : (fun z : Ω × (Fin n → Ω) => Fin.cons z.1 z.2) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0).symm := by
    funext z
    change Fin.cons z.1 z.2 = @Fin.insertNth n (fun _ => Ω) 0 z.1 z.2
    exact (Fin.insertNth_zero' z.1 z.2).symm
  rw [he]
  exact hp

private theorem measurableEmbedding_sampleCons (n : ℕ) :
    MeasurableEmbedding (fun z : Ω × (Fin n → Ω) => (Fin.cons z.1 z.2 : Fin (n + 1) → Ω)) := by
  have he : (fun z : Ω × (Fin n → Ω) => Fin.cons z.1 z.2) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0).symm := by
    funext z
    change Fin.cons z.1 z.2 = @Fin.insertNth n (fun _ => Ω) 0 z.1 z.2
    exact (Fin.insertNth_zero' z.1 z.2).symm
  rw [he]
  exact MeasurableEquiv.measurableEmbedding _

/-- Finite moments of the squared vector norm imply finite natural moments of each scalar
coordinate, including odd powers. -/
theorem hasFiniteNatMoments_coordinate_of_dotProduct {μ : Measure Ω} [IsProbabilityMeasure μ]
    {y : Ω → Fin r → ℝ} (hy : Measurable y)
    (hmom : ∀ p : ℕ, Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p) μ) (a : Fin r) :
    HasFiniteNatMoments (fun ω => y ω a) μ := by
  have heven (p : ℕ) : Integrable (fun ω => y ω a ^ (2 * p)) μ := by
    apply (hmom p).mono' (((measurable_pi_apply a).comp hy).pow_const _).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖y ω a ^ (2 * p)‖ ≤ (y ω ⬝ᵥ y ω) ^ p
    rw [Real.norm_eq_abs, abs_of_nonneg ((even_two_mul p).pow_nonneg _)]
    have hs : (y ω a) ^ 2 ≤ y ω ⬝ᵥ y ω := by
      simpa only [dotProduct, pow_two] using
        Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (y ω j))
          (Finset.mem_univ a)
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg (y ω a)) hs p
  intro p
  apply ((integrable_const (1 : ℝ)).add (heven p)).mono'
    (((measurable_pi_apply a).comp hy).pow_const _).aestronglyMeasurable
  filter_upwards [] with ω
  change ‖y ω a ^ p‖ ≤ 1 + y ω a ^ (2 * p)
  rw [Real.norm_eq_abs]
  have he : y ω a ^ (2 * p) = |y ω a ^ p| ^ 2 := by
    rw [sq_abs, ← pow_mul, Nat.mul_comm p 2]
  rw [he]
  nlinarith [sq_nonneg (|y ω a ^ p| - 1)]

/-- Centered iid covariance sums have integrable polynomial trace moments whenever the sample
has finite moments of its squared norm. -/
theorem integrable_trace_pow_rankOneCovarianceSum {μ : Measure Ω} [IsProbabilityMeasure μ]
    {y : Ω → Fin r → ℝ} (hy : Measurable y)
    (hmom : ∀ p : ℕ, Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p) μ) (n p : ℕ) :
    Integrable (fun ω : Fin n → Ω => (rankOneCovarianceSum y ω ^ p).trace)
      (Measure.pi fun _ : Fin n => μ) := by
  have hcoord (a : Fin r) := hasFiniteNatMoments_coordinate_of_dotProduct hy hmom a
  have hentry (i j : Fin r) :
      HasFiniteNatMoments (fun ω => centeredRankOneCovariance (y ω) i j) μ := by
    simpa only [centeredRankOneCovariance, Matrix.sub_apply, vecMulVec_apply, sub_eq_add_neg]
      using ((hcoord i).mul (hcoord j)).add (hasFiniteNatMoments_const (-(1 : Matrix (Fin r) (Fin r) ℝ) i j))
  have hsum (i j : Fin r) : HasFiniteNatMoments
      (fun ω : Fin n → Ω => rankOneCovarianceSum y ω i j)
      (Measure.pi fun _ : Fin n => μ) := by
    simp only [rankOneCovarianceSum, Matrix.sum_apply]
    exact HasFiniteNatMoments.sum Finset.univ fun a _ =>
      (hentry i j).comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) a)
  exact (HasFiniteNatMoments.trace_matrix_pow hsum p).integrable

private theorem integral_trace_pow_covarianceSum_succ {μ : Measure Ω} [IsProbabilityMeasure μ]
    {y : Ω → Fin r → ℝ} (hy : Measurable y)
    (hmom : ∀ p : ℕ, Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p) μ) (n p : ℕ) :
    (∫ ω : Fin (n + 1) → Ω, (rankOneCovarianceSum y ω ^ p).trace
      ∂Measure.pi fun _ : Fin (n + 1) => μ) =
    ∫ ω : Fin n → Ω, ∫ v, ((rankOneCovarianceSum y ω + centeredRankOneCovariance (y v)) ^ p).trace
      ∂μ ∂Measure.pi fun _ : Fin n => μ := by
  rw [← (measurePreserving_sampleCons μ n).integral_comp
    (measurableEmbedding_sampleCons n)]
  have hi := (measurePreserving_sampleCons μ n).integrable_comp_of_integrable
    (integrable_trace_pow_rankOneCovarianceSum hy hmom (n + 1) p)
  dsimp only [Function.comp_def] at hi
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [] with ω
  apply integral_congr_ae
  filter_upwards [] with v
  rw [rankOneCovarianceSum_cons]

/-- Normalized covariance moments are nonnegative, without an integrability side condition. -/
theorem rankOneCovarianceMoment_nonneg (y : Ω → Fin r → ℝ) (μ : Measure Ω) (n p : ℕ) :
    0 ≤ rankOneCovarianceMoment y μ n p := by
  unfold rankOneCovarianceMoment
  exact div_nonneg (integral_nonneg fun ω =>
    trace_pow_nonneg_of_even (isHermitian_rankOneCovarianceSum y ω) (even_two_mul p))
    (Nat.cast_nonneg r)

/-- The zeroth normalized trace moment is one for a positive target dimension. -/
theorem rankOneCovarianceMoment_zero {μ : Measure Ω} [IsProbabilityMeasure μ]
    (y : Ω → Fin r → ℝ) (hr : 0 < r) (n : ℕ) :
    rankOneCovarianceMoment y μ n 0 = 1 := by
  simp [rankOneCovarianceMoment, Matrix.trace_one, ne_of_gt hr]

/-- Before drawing any samples every positive-order centered moment vanishes. -/
theorem rankOneCovarianceMoment_zero_samples (y : Ω → Fin r → ℝ) (μ : Measure Ω)
    {p : ℕ} (hp : 0 < p) : rankOneCovarianceMoment y μ 0 p = 0 := by
  simp [rankOneCovarianceMoment, rankOneCovarianceSum, Nat.ne_of_gt hp]

private def covarianceMomentEnvelope (A : Matrix (Fin r) (Fin r) ℝ) (k : ℕ) : ℝ :=
  Real.sqrt ((A ^ (2 * (k / 2))).trace / r) *
    Real.sqrt ((A ^ (2 * ((k + 1) / 2))).trace / r)

private theorem integrable_covarianceMomentEnvelope {μ : Measure Ω} [IsProbabilityMeasure μ]
    {y : Ω → Fin r → ℝ} (hy : Measurable y)
    (hmom : ∀ p : ℕ, Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p) μ) (n k : ℕ) :
    Integrable (fun ω : Fin n → Ω => covarianceMomentEnvelope (rankOneCovarianceSum y ω) k)
      (Measure.pi fun _ : Fin n => μ) := by
  exact ((integrable_trace_pow_rankOneCovarianceSum hy hmom n _).div_const r).sqrt_mul_sqrt
    ((integrable_trace_pow_rankOneCovarianceSum hy hmom n _).div_const r)
    (fun ω => div_nonneg (trace_pow_nonneg_of_even
      (isHermitian_rankOneCovarianceSum y ω) (even_two_mul _)) (Nat.cast_nonneg r))
    (fun ω => div_nonneg (trace_pow_nonneg_of_even
      (isHermitian_rankOneCovarianceSum y ω) (even_two_mul _)) (Nat.cast_nonneg r))

private theorem integral_covarianceMomentEnvelope_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {y : Ω → Fin r → ℝ} (hy : Measurable y)
    (hmom : ∀ p : ℕ, Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p) μ) (n k : ℕ) :
    (∫ ω : Fin n → Ω, covarianceMomentEnvelope (rankOneCovarianceSum y ω) k
      ∂Measure.pi fun _ : Fin n => μ) ≤ evenMomentInterpolation (rankOneCovarianceMoment y μ n) k := by
  have hb := integral_sqrt_mul_sqrt_le
    ((integrable_trace_pow_rankOneCovarianceSum hy hmom n (2 * (k / 2))).div_const r)
    ((integrable_trace_pow_rankOneCovarianceSum hy hmom n (2 * ((k + 1) / 2))).div_const r)
    (fun ω => div_nonneg (trace_pow_nonneg_of_even
      (isHermitian_rankOneCovarianceSum y ω) (even_two_mul _)) (Nat.cast_nonneg r))
    (fun ω => div_nonneg (trace_pow_nonneg_of_even
      (isHermitian_rankOneCovarianceSum y ω) (even_two_mul _)) (Nat.cast_nonneg r))
  simpa only [covarianceMomentEnvelope, evenMomentInterpolation, rankOneCovarianceMoment,
    integral_div] using hb

/-- A one-sample centered matrix trace estimate implies the factorial recurrence for the
actual iid covariance process. All sample integrability follows from finite squared-norm
moments; no eigenvector measurability is required. -/
theorem rankOneCovarianceMoment_succ_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {y : Ω → Fin r → ℝ} (hy : Measurable y)
    (hmom : ∀ p : ℕ, Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p) μ)
    (hr : 0 < r) {ν R : ℝ} (hν : 0 ≤ ν) (hR : 0 ≤ R) (n p : ℕ)
    (hstep : ∀ A : Matrix (Fin r) (Fin r) ℝ, A.IsHermitian →
      (∫ v, ((A + centeredRankOneCovariance (y v)) ^ (2 * p)).trace ∂μ) ≤
        (A ^ (2 * p)).trace + ∑ k ∈ Finset.range (2 * p - 1),
          ((2 * p).choose (k + 2) : ℝ) * ((k + 2).factorial : ℝ) / 2 * ν * R ^ k *
            (cfc (fun x : ℝ => |x| ^ (2 * p - (k + 2))) A).trace) :
    rankOneCovarianceMoment y μ (n + 1) p ≤
      rankOneCovarianceMoment y μ n p + finiteMomentUpdate ν R (rankOneCovarianceMoment y μ n) p := by
  let C (k : ℕ) : ℝ :=
    ((2 * p).choose (k + 2) : ℝ) * ((k + 2).factorial : ℝ) / 2 * ν * R ^ k
  have hC (k : ℕ) : 0 ≤ C k := by dsimp [C]; positivity
  have hpoint (ω : Fin n → Ω) :
      (∫ v, ((rankOneCovarianceSum y ω + centeredRankOneCovariance (y v)) ^ (2 * p)).trace ∂μ) / r ≤
      (rankOneCovarianceSum y ω ^ (2 * p)).trace / r +
        ∑ k ∈ Finset.range (2 * p - 1), C k *
          covarianceMomentEnvelope (rankOneCovarianceSum y ω) (2 * p - (k + 2)) := by
    have ha := isHermitian_rankOneCovarianceSum y ω
    have hb := div_le_div_of_nonneg_right (hstep _ ha) (Nat.cast_nonneg r)
    rw [add_div, Finset.sum_div] at hb
    apply hb.trans
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro k _
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_trace_cfc_abs_pow_le_sqrt_div_trace_even_pow ha _ (by positivity : (0 : ℝ) < r)) (hC k)
  have hi := (measurePreserving_sampleCons μ n).integrable_comp_of_integrable
    (integrable_trace_pow_rankOneCovarianceSum hy hmom (n + 1) (2 * p))
  have hint : Integrable (fun ω : Fin n → Ω =>
      (∫ v, ((rankOneCovarianceSum y ω + centeredRankOneCovariance (y v)) ^ (2 * p)).trace ∂μ) / r)
      (Measure.pi fun _ : Fin n => μ) := by
    simpa only [Function.comp_def, rankOneCovarianceSum_cons] using
      hi.integral_prod_right.div_const (r : ℝ)
  have henv := fun k => integrable_covarianceMomentEnvelope hy hmom n (2 * p - (k + 2))
  have hs := integrable_finsetSum (Finset.range (2 * p - 1))
    (fun k _ => (henv k).const_mul (C k))
  have hbase := (integrable_trace_pow_rankOneCovarianceSum hy hmom n (2 * p)).div_const (r : ℝ)
  have hmono := integral_mono hint (hbase.add hs) hpoint
  simp only [Pi.add_apply] at hmono
  rw [integral_add hbase hs, integral_finsetSum _ (fun k _ => (henv k).const_mul (C k))] at hmono
  simp_rw [integral_const_mul] at hmono
  simp only [integral_div] at hmono
  have henvbound :
      (∑ k ∈ Finset.range (2 * p - 1), C k *
        ∫ ω : Fin n → Ω, covarianceMomentEnvelope (rankOneCovarianceSum y ω)
          (2 * p - (k + 2)) ∂Measure.pi fun _ : Fin n => μ) ≤
      finiteMomentUpdate ν R (rankOneCovarianceMoment y μ n) p := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (integral_covarianceMomentEnvelope_le hy hmom n _) (hC k)
  calc
    rankOneCovarianceMoment y μ (n + 1) p =
        ∫ ω : Fin n → Ω,
          (∫ v, ((rankOneCovarianceSum y ω + centeredRankOneCovariance (y v)) ^ (2 * p)).trace ∂μ) / r
          ∂Measure.pi fun _ : Fin n => μ := by
      rw [rankOneCovarianceMoment, integral_trace_pow_covarianceSum_succ hy hmom, integral_div]
    _ ≤ _ := by
      rw [integral_div]
      exact hmono.trans (add_le_add le_rfl henvbound)

/-- The iid covariance moment bound obtained from the actual one-step trace estimate and
the finite factorial recurrence. The constants retain the square-root variance scale and
the linear radius scale. -/
theorem rankOneCovarianceMoment_le_sqrt_add_mul_pow {μ : Measure Ω} [IsProbabilityMeasure μ]
    {y : Ω → Fin r → ℝ} (hy : Measurable y)
    (hmom : ∀ p : ℕ, Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p) μ)
    (hr : 0 < r) {ν R : ℝ} (hν : 0 < ν) (hR : 0 ≤ R) {q m : ℕ}
    (hq : 1 ≤ q) (hm : 1 ≤ m)
    (hstep : ∀ p, 1 ≤ p → p ≤ q → ∀ A : Matrix (Fin r) (Fin r) ℝ, A.IsHermitian →
      (∫ v, ((A + centeredRankOneCovariance (y v)) ^ (2 * p)).trace ∂μ) ≤
        (A ^ (2 * p)).trace + ∑ k ∈ Finset.range (2 * p - 1),
          ((2 * p).choose (k + 2) : ℝ) * ((k + 2).factorial : ℝ) / 2 * ν * R ^ k *
            (cfc (fun x : ℝ => |x| ^ (2 * p - (k + 2))) A).trace) :
    rankOneCovarianceMoment y μ m q ≤
      (2 * Real.sqrt ((q : ℝ) * ν * m) + 2 * (q : ℝ) * R) ^ (2 * q) := by
  apply le_sqrt_add_mul_pow_of_finiteMomentUpdate hν hR hq hm
    (rankOneCovarianceMoment_nonneg y μ)
    (rankOneCovarianceMoment_zero y hr)
  · intro p hp _
    exact rankOneCovarianceMoment_zero_samples y μ (by omega)
  · intro n p hp hpq
    exact rankOneCovarianceMoment_succ_le hy hmom hr hν.le hR n p (hstep p hp hpq)

/-- Markov's inequality for the spectral norm of an iid centered covariance sum, given its
normalized trace moment. -/
theorem measureReal_lt_specNorm_rankOneCovarianceSum_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {y : Ω → Fin r → ℝ} (hy : Measurable y)
    (hmom : ∀ p : ℕ, Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p) μ)
    {m q : ℕ} (hq : 0 < q) {t : ℝ} (ht : 0 < t) :
    (Measure.pi fun _ : Fin m => μ).real {ω | t < specNorm (rankOneCovarianceSum y ω)} ≤
      (r : ℝ) * rankOneCovarianceMoment y μ m q / t ^ (2 * q) := by
  let μm := Measure.pi fun _ : Fin m => μ
  have hi := integrable_trace_pow_rankOneCovarianceSum hy hmom m (2 * q)
  have hnonneg (ω : Fin m → Ω) :=
    trace_pow_nonneg_of_even (isHermitian_rankOneCovarianceSum y ω) (even_two_mul q)
  have hevent : {ω : Fin m → Ω | t < specNorm (rankOneCovarianceSum y ω)} ⊆
      {ω | t ^ (2 * q) ≤ (rankOneCovarianceSum y ω ^ (2 * q)).trace} := by
    intro ω hω
    exact (pow_le_pow_left₀ ht.le hω.le _).trans
      (specNorm_pow_two_mul_le_trace_pow (isHermitian_rankOneCovarianceSum y ω) hq)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hnonneg) hi (t ^ (2 * q))
  have hprob := measureReal_mono (μ := μm) hevent
  have hmul := (mul_le_mul_of_nonneg_left hprob (pow_nonneg ht.le (2 * q))).trans hm
  apply (le_div_iff₀ (pow_pos ht (2 * q))).2
  rw [mul_comm]
  have htrace : (∫ ω : Fin m → Ω, (rankOneCovarianceSum y ω ^ (2 * q)).trace ∂μm) =
      (r : ℝ) * rankOneCovarianceMoment y μ m q := by
    by_cases hr : r = 0
    · subst r
      simp [Matrix.trace, rankOneCovarianceMoment]
    · unfold rankOneCovarianceMoment
      rw [mul_div_cancel₀ _ (by exact_mod_cast hr : (r : ℝ) ≠ 0)]
  rw [← htrace]
  exact hmul

open scoped Matrix.Norms.L2Operator in
/-- A finite-moment concentration bound for the empirical covariance of actual iid vector
samples. A source one-step trace estimate yields a spectral failure probability with the
variance and radius scales `2√(qνm)+2qR`. -/
theorem measureReal_lt_specNorm_smul_rankOneCovarianceSum_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {y : Ω → Fin r → ℝ} (hy : Measurable y)
    (hmom : ∀ p : ℕ, Integrable (fun ω => (y ω ⬝ᵥ y ω) ^ p) μ)
    (hr : 0 < r) {ν R : ℝ} (hν : 0 < ν) (hR : 0 ≤ R) {q m : ℕ}
    (hq : 1 ≤ q) (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε)
    (hstep : ∀ p, 1 ≤ p → p ≤ q → ∀ A : Matrix (Fin r) (Fin r) ℝ, A.IsHermitian →
      (∫ v, ((A + centeredRankOneCovariance (y v)) ^ (2 * p)).trace ∂μ) ≤
        (A ^ (2 * p)).trace + ∑ k ∈ Finset.range (2 * p - 1),
          ((2 * p).choose (k + 2) : ℝ) * ((k + 2).factorial : ℝ) / 2 * ν * R ^ k *
            (cfc (fun x : ℝ => |x| ^ (2 * p - (k + 2))) A).trace) :
    (Measure.pi fun _ : Fin m => μ).real
      {ω | ε < specNorm ((m : ℝ)⁻¹ • rankOneCovarianceSum y ω)} ≤
      (r : ℝ) * ((2 * Real.sqrt ((q : ℝ) * ν * m) + 2 * (q : ℝ) * R) /
        ((m : ℝ) * ε)) ^ (2 * q) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have he : {ω : Fin m → Ω | ε < specNorm ((m : ℝ)⁻¹ • rankOneCovarianceSum y ω)} =
      {ω | (m : ℝ) * ε < specNorm (rankOneCovarianceSum y ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, specNorm_eq_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hmR.le)]
    exact lt_inv_mul_iff₀ hmR
  rw [he]
  have hbar := rankOneCovarianceMoment_le_sqrt_add_mul_pow hy hmom hr hν hR hq hm hstep
  calc
    _ ≤ (r : ℝ) * rankOneCovarianceMoment y μ m q / ((m : ℝ) * ε) ^ (2 * q) :=
      measureReal_lt_specNorm_rankOneCovarianceSum_le hy hmom (by omega) (mul_pos hmR hε)
    _ ≤ (r : ℝ) * (2 * Real.sqrt ((q : ℝ) * ν * m) + 2 * (q : ℝ) * R) ^ (2 * q) /
        ((m : ℝ) * ε) ^ (2 * q) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbar (Nat.cast_nonneg r))
        (pow_nonneg (mul_nonneg hmR.le hε.le) _)
    _ = _ := by rw [div_pow]; ring

end NLAlib
