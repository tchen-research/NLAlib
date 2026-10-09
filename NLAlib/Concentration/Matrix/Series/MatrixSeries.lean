import NLAlib.Concentration.Matrix.Defs.ScalarLaws
import NLAlib.Concentration.Matrix.Defs.Calculus
import NLAlib.Concentration.Matrix.Defs.Dilation
import NLAlib.Concentration.Matrix.Series.HermitianSeries
import NLAlib.Concentration.Matrix.Bernstein.DilationIdentities
import NLAlib.Concentration.Matrix.Bernstein.DilationVariance
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Theorem 4.1.1 — Matrix Gaussian and Rademacher series

Main declaration: `NLAlib.matrix_gaussian_series`.

Atlas: `matrix-gaussian-series`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 4.1.1, equations (4.1.2–6), printed p. 42.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace NLAlib

open NLAlib

/-- Second moments of the scalar coefficients. -/
private lemma scalar_package {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (g : Fin N → Ω → ℝ) (hMeas : ∀ k, Measurable (g k))
    (hLaw : (∀ k, IsStandardGaussian μ (g k)) ∨ (∀ k, IsRademacher μ (g k))) (k : Fin N) :
    MemLp (g k) 2 μ ∧ ∫ ω, g k ω ∂μ = 0 ∧ ∫ ω, g k ω * g k ω ∂μ = 1 := by
  rcases hLaw with h | h
  · have hk : μ.map (g k) = gaussianReal 0 1 := h k
    refine ⟨?_, ?_, ?_⟩
    · have := memLp_id_gaussianReal (μ := 0) (v := 1) 2
      rw [← hk, memLp_map_measure_iff aestronglyMeasurable_id (hMeas k).aemeasurable] at this
      simpa using this
    · have := integral_id_gaussianReal (μ := 0) (v := 1)
      rw [← hk, integral_map (f := fun x : ℝ => x) (hMeas k).aemeasurable (by fun_prop)] at this
      simpa using this
    · have h1 := variance_fun_id_gaussianReal (μ := 0) (v := 1)
      rw [variance_of_integral_eq_zero aemeasurable_id' integral_id_gaussianReal] at h1
      rw [← hk, integral_map (hMeas k).aemeasurable (by fun_prop)] at h1
      simpa [sq] using h1
  · have hk : μ.map (g k) = (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
        (1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ) := h k
    have hms : MeasurableSet {x : ℝ | x = 1 ∨ x = -1} :=
      (measurableSet_singleton (1 : ℝ)).union (measurableSet_singleton (-1 : ℝ))
    have hae : ∀ᵐ x ∂(μ.map (g k)), x = 1 ∨ x = -1 := by
      rw [hk, ae_add_measure_iff]
      exact ⟨Measure.ae_smul_measure ((ae_dirac_iff hms).2 (Or.inl rfl)) _,
        Measure.ae_smul_measure ((ae_dirac_iff hms).2 (Or.inr rfl)) _⟩
    have hae' : ∀ᵐ ω ∂μ, g k ω = 1 ∨ g k ω = -1 := ae_of_ae_map (hMeas k).aemeasurable hae
    refine ⟨?_, ?_, ?_⟩
    · refine MemLp.of_bound (hMeas k).aestronglyMeasurable 1 ?_
      filter_upwards [hae'] with ω hω
      rcases hω with h | h <;> simp [h]
    · have hI : ∀ a : ℝ, Integrable (fun x : ℝ => x) ((1 / 2 : ENNReal) • Measure.dirac a) :=
        fun a => (integrable_dirac (by simp)).smul_measure (by simp)
      have : ∫ x, x ∂(μ.map (g k)) = 0 := by
        rw [hk, integral_add_measure (hI 1) (hI (-1)), integral_smul_measure,
          integral_smul_measure, integral_dirac, integral_dirac]
        norm_num
      rwa [integral_map (f := fun x : ℝ => x) (hMeas k).aemeasurable (by fun_prop)] at this
    · have : (fun ω => g k ω * g k ω) =ᵐ[μ] fun _ => (1 : ℝ) := by
        filter_upwards [hae'] with ω hω
        rcases hω with h | h <;> simp [h]
      rw [integral_congr_ae this]
      simp

/-- The second-moment identity for a series with orthonormal scalar coefficients. -/
private lemma second_moment_series {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {N p q r : ℕ}
    (g : Fin N → Ω → ℝ) (hint : ∀ j k, Integrable (fun ω => g j ω * g k ω) μ)
    (hcorr : ∀ j k, ∫ ω, g j ω * g k ω ∂μ = if j = k then 1 else 0)
    (X : Fin N → Matrix (Fin p) (Fin q) ℂ) (Y : Fin N → Matrix (Fin q) (Fin r) ℂ) :
    ∫ ω, (∑ j, g j ω • X j) * (∑ k, g k ω • Y k) ∂μ = ∑ k, X k * Y k := by
  have h1 : ∀ ω, (∑ j, g j ω • X j) * (∑ k, g k ω • Y k) =
      ∑ j, ∑ k, (g j ω * g k ω) • (X j * Y k) := by
    intro ω
    rw [Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp_rw [h1]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun k _ => (hint j k).smul_const _))]
  have h2 : ∀ j, ∫ ω, ∑ k, (g j ω * g k ω) • (X j * Y k) ∂μ = X j * Y j := by
    intro j
    rw [integral_finsetSum _ (fun k _ => (hint j k).smul_const _)]
    simp_rw [integral_smul_const, hcorr, ite_smul, one_smul, zero_smul]
    simp
  simp_rw [h2]

end NLAlib

open NLAlib

/-- Matrix Gaussian and Rademacher series, rectangular case: for `Z = ∑ k, g k • B k` the variance is
the maximum of the two row/column sums, `𝔼 ‖Z‖ ≤ √(2 v log (m + n))`, and `P{‖Z‖ ≥ t} ≤
gaussianSeriesTail (m + n) v t`.

Tropp 2015, Thm 4.1.1. Atlas: `matrix-gaussian-series`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 4*.

Gaussian and Rademacher coefficients are covered by one statement through the disjunctive law
hypothesis. -/
theorem NLAlib.matrix_gaussian_series {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n N : ℕ} [NeZero m] [NeZero n]
    (B : Fin N → Matrix (Fin m) (Fin n) ℂ)
    (g : Fin N → Ω → ℝ) (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ)
    (hLaw : (∀ k, IsStandardGaussian μ (g k)) ∨ (∀ k, IsRademacher μ (g k))) :
    let Z := fun ω => ∑ k, g k ω • B k
    let v := rectSecondMoment μ Z
    v = max (spectralNorm (∑ k, B k * (B k).conjTranspose))
      (spectralNorm (∑ k, (B k).conjTranspose * B k)) ∧
    (∫ ω, spectralNorm (Z ω) ∂μ) ≤ Real.sqrt (2 * v * Real.log (m + n)) ∧
    ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ spectralNorm (Z ω)}).toReal ≤
      gaussianSeriesTail (m + n) v t := by
  intro Z v
  have hpkg := scalar_package μ g hMeas hLaw
  have hint : ∀ j k, Integrable (fun ω => g j ω * g k ω) μ := fun j k =>
    (hpkg j).1.integrable_mul (hpkg k).1
  have hcorr : ∀ j k, ∫ ω, g j ω * g k ω ∂μ = if j = k then 1 else 0 := by
    intro j k
    split_ifs with hjk
    · subst hjk; exact (hpkg j).2.2
    · rw [IndepFun.integral_fun_mul_eq_mul_integral (hIndep.indepFun hjk)
        (hMeas j).aestronglyMeasurable (hMeas k).aestronglyMeasurable, (hpkg j).2.1, zero_mul]
  -- Step 1: the variance statistic of `Z`.
  have hZh : ∀ ω, (Z ω).conjTranspose = ∑ k, g k ω • (B k).conjTranspose := by
    intro ω
    simp [Z, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  have hZZ : ∫ ω, Z ω * (Z ω).conjTranspose ∂μ = ∑ k, B k * (B k).conjTranspose := by
    simp_rw [hZh]
    exact second_moment_series μ g hint hcorr B (fun k => (B k).conjTranspose)
  have hZhZ : ∫ ω, (Z ω).conjTranspose * Z ω ∂μ = ∑ k, (B k).conjTranspose * B k := by
    simp_rw [hZh]
    exact second_moment_series μ g hint hcorr (fun k => (B k).conjTranspose) B
  have hv1 : v = max (spectralNorm (∑ k, B k * (B k).conjTranspose))
      (spectralNorm (∑ k, (B k).conjTranspose * B k)) := by
    show max (spectralNorm (∫ ω, Z ω * (Z ω).conjTranspose ∂μ))
      (spectralNorm (∫ ω, (Z ω).conjTranspose * Z ω ∂μ)) = _
    rw [hZZ, hZhZ]
  -- Step 2: `Z` is centered, measurable and square integrable.
  have hZint : ∫ ω, Z ω ∂μ = 0 := by
    simp only [Z]
    rw [integral_finsetSum _ (fun k _ => ((hpkg k).1.integrable (by norm_num)).smul_const _)]
    simp [integral_smul_const, (hpkg _).2.1]
  have hZmeas : Measurable Z :=
    Finset.measurable_sum _ (fun k _ => (hMeas k).smul_const (B k))
  have hZL2 : MemLp Z 2 μ :=
    memLp_finsetSum _ (fun k _ => (memLp_const (p := ⊤) (B k)).smul (hpkg k).1)
  have hdv := hermitianSecondMoment_dilation_eq_rectSecondMoment μ Z hZmeas hZL2
  rw [hZint] at hdv
  simp only [sub_zero] at hdv
  -- Step 3: transport the Hermitian dilation to `Fin (m + n)`.
  have : NeZero (m + n) := ⟨by have := NeZero.ne m; omega⟩
  let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  let A : Fin N → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun k => Matrix.reindex e e (dilation (B k))
  have hA : ∀ k, (A k).IsHermitian := fun k =>
    (dilation_identities (B k)).1.submatrix _
  have hY : ∀ ω, ∑ k, g k ω • A k = Matrix.reindex e e (dilation (Z ω)) := by
    intro ω
    rw [← Matrix.coe_reindexLinearEquiv ℝ ℂ e e, ← dilationLinearMap_apply]
    simp only [Z, map_sum, map_smul, A, dilationLinearMap_apply, Matrix.coe_reindexLinearEquiv]
  have hlam : ∀ ω, lambdaMax (∑ k, g k ω • A k) = spectralNorm (Z ω) := by
    intro ω
    rw [hY ω, lambdaMax_reindex]
    exact (dilation_identities (Z ω)).2.2.1.trans (dilation_identities (Z ω)).2.2.2
  have hvY : hermitianSecondMoment μ (fun ω => ∑ k, g k ω • A k) = v := by
    have hsq : ∀ ω, (Matrix.reindex e e (dilation (Z ω))) ^ 2 =
        Matrix.reindex e e (dilation (Z ω) ^ 2) := by
      intro ω
      rw [← Matrix.coe_reindexAlgEquiv ℝ, map_pow]
    unfold hermitianSecondMoment
    simp_rw [hY, hsq]
    rw [integral_reindex, spectralNorm, norm_reindex]
    exact hdv
  have H := hermitian_gaussian_series μ A hA g hMeas hIndep hLaw
  obtain ⟨-, H2, H3⟩ := H
  refine ⟨hv1, ?_, ?_⟩
  · simp only [hlam, hvY] at H2
    simpa [Nat.cast_add] using H2
  · intro t ht
    have := H3 t ht
    simp only [hlam, hvY] at this
    exact this
