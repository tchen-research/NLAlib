import NLAlib.Probability.Concentration.Matrix.MasterBounds
import NLAlib.Probability.Concentration.Matrix.GaussianMgfCgf
import NLAlib.Probability.Concentration.Matrix.RademacherMgfCgf
import NLAlib.Probability.SubGaussian.EvenMoments
import NLAlib.Matrix.Functions.TraceExpMonotone
import NLAlib.Matrix.Functions.TraceExpBounds
/-!
# Theorem 4.6.1 — Hermitian series with sub-Gaussian coefficients

For `Y = ∑ k, g k • A k` with Hermitian `A k` and independent `1`-sub-Gaussian coefficients
`g k` (standard Gaussian or Rademacher coefficients are the corollaries):

* `hermitianSecondMoment_hermitianSeries_eq`: `‖𝔼 Y²‖ = ‖∑ A k²‖` when `𝔼 (g k)² = 1`;
* `integral_lambdaMax_hermitianSeries_le`: `𝔼 λmax(Y) ≤ √(2 v log d)` with `v = ‖∑ A k²‖`;
* `measureReal_lambdaMax_hermitianSeries_ge_le`: `P{λmax(Y) ≥ t} ≤ gaussianSeriesTail d v t`;
* the `…_of_hasLaw_gaussianReal` and `…_of_hasLaw_rademacherMeasure` corollaries.

Atlas: `matrix-gaussian-series`. Source: Tropp 2015, *An Introduction to Matrix Concentration
Inequalities*, Theorem 4.6.1, equations (4.6.1–3). Tropp states the theorem for Gaussian and
Rademacher coefficients; the proof only uses the sub-Gaussian mgf bound of Lemmas 4.6.2–4.6.3 and
is stated at that generality.
-/
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder ComplexOrder

namespace NLAlib

open scoped Matrix.Norms.L2Operator in
private lemma norm_exp_le {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (s : ℝ) : ‖matrixExp (s • A)‖ ≤ Real.exp (s * ‖A‖) + Real.exp (-(s * ‖A‖)) := by
  have hsA : (s • A).IsHermitian := hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))
  have h1 : ‖matrixExp (s • A)‖ ≤ Real.exp (|s| * ‖A‖) := by
    rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hsA]
    apply norm_cfc_le (Real.exp_pos _).le
    intro x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
    apply Real.exp_le_exp.mpr
    calc x ≤ |x| := le_abs_self x
      _ ≤ ‖s • A‖ := abs_le_norm_of_mem_spectrum _ hx
      _ = |s| * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs]
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs] at h1
    linarith [Real.exp_pos (-(s * ‖A‖))]
  · rw [abs_of_nonpos hs, neg_mul] at h1
    linarith [Real.exp_pos (s * ‖A‖)]

open scoped Matrix.Norms.L2Operator in
private lemma exp_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (g : Ω → ℝ) (hg : Measurable g)
    (hexp : ∀ c : ℝ, Integrable (fun ω => Real.exp (c * g ω)) μ) (θ : ℝ) :
    Integrable (fun ω => matrixExp (θ • (g ω • A))) μ := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have e : (fun ω => matrixExp (θ • (g ω • A))) = fun ω => matrixExp ((θ * g ω) • A) := by
    funext ω
    rw [smul_smul]
  rw [e]
  have hb : Integrable (fun ω => Real.exp ((θ * ‖A‖) * g ω) +
      Real.exp ((-(θ * ‖A‖)) * g ω)) μ := (hexp _).add (hexp _)
  refine hb.mono' ?_ ?_
  · have hcont : Continuous (fun s : ℝ => matrixExp (s • A)) := by
      dsimp [matrixExp]
      fun_prop
    exact hcont.comp_aestronglyMeasurable (measurable_const.mul hg).aestronglyMeasurable
  · refine ae_of_all _ (fun ω => ?_)
    have h := norm_exp_le A hA (θ * g ω)
    have e1 : θ * ‖A‖ * g ω = θ * g ω * ‖A‖ := by ring
    have e2 : -(θ * ‖A‖) * g ω = -(θ * g ω * ‖A‖) := by ring
    simp only [e1, e2]
    exact h

open scoped Matrix.Norms.L2Operator in
/-- The second moment of a series with independent, centred, unit-variance coefficients. -/
theorem integral_sum_smul_sq_eq_sum_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {d : Type*} [Fintype d] [DecidableEq d] {N : ℕ}
    (A : Fin N → Matrix d d ℂ)
    (g : Fin N → Ω → ℝ) (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (h2 : ∀ k, MemLp (g k) 2 μ) (h0 : ∀ k, ∫ ω, g k ω ∂μ = 0)
    (h1 : ∀ k, ∫ ω, g k ω ^ 2 ∂μ = 1) :
    ∫ ω, (∑ k, g k ω • A k) ^ 2 ∂μ = ∑ k, A k ^ 2 := by
  have hexp : ∀ ω, (∑ k, g k ω • A k) ^ 2 = ∑ j, ∑ k, (g j ω * g k ω) • (A j * A k) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm]
  have hint : ∀ j k, Integrable (fun ω => g j ω * g k ω) μ := fun j k =>
    (h2 j).integrable_mul (h2 k)
  have hcorr : ∀ j k, ∫ ω, g j ω * g k ω ∂μ = if j = k then 1 else 0 := by
    intro j k
    split_ifs with hjk
    · subst hjk
      simpa [sq] using h1 j
    · rw [(hIndep.indepFun hjk).integral_fun_mul_eq_mul_integral
        (hMeas j).aestronglyMeasurable (hMeas k).aestronglyMeasurable, h0 j, zero_mul]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => (hint j k).smul_const _))]
  have hinner : ∀ j, ∫ ω, ∑ k, (g j ω * g k ω) • (A j * A k) ∂μ = A j ^ 2 := by
    intro j
    rw [integral_finsetSum _ (fun k _ => (hint j k).smul_const _)]
    simp_rw [integral_smul_const, hcorr]
    simp [sq]
  simp_rw [hinner]

private lemma scalar {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ θ : ℝ, 0 < θ → x ≤ a / θ + θ * b / 2) : x ≤ Real.sqrt (2 * b * a) := by
  by_contra hcon
  push Not at hcon
  have hs0 := Real.sqrt_nonneg (2 * b * a)
  have hx : 0 < x := lt_of_le_of_lt hs0 hcon
  rcases ha.eq_or_lt with rfl | ha'
  · rcases hb.eq_or_lt with rfl | hb'
    · have := h 1 one_pos
      simp at this
      linarith
    · have := h (x / b) (div_pos hx hb')
      rw [zero_div, zero_add, div_mul_cancel₀ _ hb'.ne'] at this
      linarith
  · rcases hb.eq_or_lt with rfl | hb'
    · have := h (2 * a / x) (by positivity)
      have e : a / (2 * a / x) = x / 2 := by field_simp
      rw [e] at this
      simp at this
      linarith
    · have hs : 0 < Real.sqrt (2 * b * a) := Real.sqrt_pos.mpr (by positivity)
      have hss : Real.sqrt (2 * b * a) ^ 2 = 2 * b * a := Real.sq_sqrt (by positivity)
      have := h (Real.sqrt (2 * b * a) / b) (div_pos hs hb')
      generalize Real.sqrt (2 * b * a) = s at hs hss this hcon
      have e : a / (s / b) + s / b * b / 2 = s := by
        field_simp
        nlinarith [hss]
      linarith

section HermitianSeries

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ}
  [NeZero d] (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (g : Fin N → Ω → ℝ)

open scoped Matrix.Norms.L2Operator in
/-- **Variance of a Hermitian series**: for independent centred unit-variance coefficients,
`hermitianSecondMoment μ (∑ k, g k • A k) = ‖∑ k, A k ^ 2‖`. Tropp 2015, eq. (4.6.1).
atlas: matrix-gaussian-series -/
theorem hermitianSecondMoment_hermitianSeries_eq (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ) (hSG : ∀ k, HasSubgaussianMGF (g k) 1 μ)
    (hVar : ∀ k, ∫ ω, g k ω ^ 2 ∂μ = 1) :
    hermitianSecondMoment μ (fun ω => ∑ k, g k ω • A k) = specNorm (∑ k, A k ^ 2) := by
  unfold hermitianSecondMoment
  rw [integral_sum_smul_sq_eq_sum_sq μ A g hMeas hIndep (fun k => (hSG k).memLp 2)
    (fun k => integral_eq_zero_of_hasSubgaussianMGF (hSG k)) hVar]

open scoped Matrix.Norms.L2Operator in
/-- The cumulant sum of a sub-Gaussian Hermitian series is bounded by `d e^{θ² v / 2}`. -/
private lemma traceExp_cumulantSum_le (hA : ∀ k, (A k).IsHermitian)
    (hSG : ∀ k, HasSubgaussianMGF (g k) 1 μ) (θ : ℝ) :
    traceExp (cumulantSum μ (fun k ω => g k ω • A k) θ) ≤
      d * Real.exp (θ ^ 2 / 2 * specNorm (∑ k, A k ^ 2)) := by
  have hBherm : (∑ k, A k ^ 2).IsHermitian := isSelfAdjoint_sum _ (fun k _ => (hA k).pow 2)
  have hcumH : (cumulantSum μ (fun k ω => g k ω • A k) θ).IsHermitian :=
    isSelfAdjoint_sum _ (fun k _ => by unfold matrixLog; exact IsSelfAdjoint.cfc)
  have hk : ∀ k, (matrixLog (∫ ω, matrixExp (θ • (g k ω • A k)) ∂μ)) ≤
      ((θ ^ 2 / 2) • A k ^ 2) := by
    intro k
    have e : (fun ω => matrixExp (θ • (g k ω • A k))) =
        fun ω => matrixExp ((θ * g k ω) • A k) := by
      funext ω
      simp only [smul_smul]
    rw [e]
    exact matrixLog_integral_matrixExp_smul_le_of_hasSubgaussianMGF (A k) (hA k) (hSG k) θ
  have hsum : (cumulantSum μ (fun k ω => g k ω • A k) θ) ≤ ((θ ^ 2 / 2) • ∑ k, A k ^ 2) := by
    unfold cumulantSum
    rw [Matrix.le_iff]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Matrix.posSemidef_sum _ (fun k _ => hk k)
  have hBH' : ((θ ^ 2 / 2) • ∑ k, A k ^ 2).IsHermitian :=
    hBherm.smul (isSelfAdjoint_iff.mpr (star_trivial _))
  calc traceExp (cumulantSum μ (fun k ω => g k ω • A k) θ)
      ≤ traceExp ((θ ^ 2 / 2) • ∑ k, A k ^ 2) := traceExp_le_traceExp _ _ hcumH hBH' hsum
    _ ≤ d * Real.exp (θ ^ 2 / 2 * ‖∑ k, A k ^ 2‖) :=
        traceExp_smul_le_mul_exp_mul_norm _ hBherm (by positivity)
    _ = d * Real.exp (θ ^ 2 / 2 * specNorm (∑ k, A k ^ 2)) := by rw [specNorm_eq_norm]

open scoped Matrix.Norms.L2Operator in
/-- The master-bound package for a sub-Gaussian Hermitian series. -/
private lemma master_package (hA : ∀ k, (A k).IsHermitian) (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ) (hSG : ∀ k, HasSubgaussianMGF (g k) 1 μ) (θ : ℝ) :
    (∀ k, Measurable (fun ω => g k ω • A k)) ∧
    (∀ k, ∀ᵐ ω ∂μ, (g k ω • A k).IsHermitian) ∧
    (∀ k, Integrable (fun ω => g k ω • A k) μ) ∧
    iIndepFun (fun k ω => g k ω • A k) μ ∧
    (∀ k, Integrable (fun ω => matrixExp (θ • (g k ω • A k))) μ) := by
  have hsmulMeas : ∀ k, Measurable (fun s : ℝ => s • A k) := fun k =>
    (continuous_id.smul continuous_const).measurable
  refine ⟨fun k => (hsmulMeas k).comp (hMeas k), fun k =>
    ae_of_all _ (fun ω => (hA k).smul (isSelfAdjoint_iff.mpr (star_trivial _))),
    fun k => ((hSG k).integrable).smul_const (A k),
    hIndep.comp (fun k s => s • A k) hsmulMeas, fun k =>
    exp_integrable μ (A k) (hA k) (g k) (hMeas k) (hSG k).integrable_exp_mul θ⟩

/-- **Hermitian series, expectation bound**: for independent `1`-sub-Gaussian coefficients and
Hermitian `A k`, `𝔼 λmax(∑ k, g k • A k) ≤ √(2 ‖∑ k, A k ^ 2‖ log d)`. Tropp 2015, Thm 4.6.1,
eq. (4.6.2).
atlas: matrix-gaussian-series -/
theorem integral_lambdaMax_hermitianSeries_le (hA : ∀ k, (A k).IsHermitian)
    (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hSG : ∀ k, HasSubgaussianMGF (g k) 1 μ) :
    (∫ ω, lambdaMax (∑ k, g k ω • A k) ∂μ) ≤
      Real.sqrt (2 * specNorm (∑ k, A k ^ 2) * Real.log d) := by
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le one_pos hd
  set v := specNorm (∑ k, A k ^ 2) with hv
  have hv0 : 0 ≤ v := specNorm_nonneg _
  refine scalar (Real.log_nonneg hd) hv0 (fun θ hθ => ?_)
  obtain ⟨hXMeas, hXHerm, hXInt, hXIndep, hXExp⟩ := master_package μ A g hA hMeas hIndep hSG θ
  have h1 := integral_lambdaMax_sum_le_log_traceExp_cumulantSum_div μ (fun k ω => g k ω • A k)
    hθ hXMeas hXHerm hXInt hXIndep hXExp
  have hcumH : (cumulantSum μ (fun k ω => g k ω • A k) θ).IsHermitian :=
    isSelfAdjoint_sum _ (fun k _ => by unfold matrixLog; exact IsSelfAdjoint.cfc)
  have hpos : 0 < traceExp (cumulantSum μ (fun k ω => g k ω • A k) θ) :=
    traceExp_pos_of_isHermitian _ hcumH
  have hlog : Real.log (traceExp (cumulantSum μ (fun k ω => g k ω • A k) θ)) ≤
      Real.log d + θ ^ 2 / 2 * v := by
    calc _ ≤ Real.log (d * Real.exp (θ ^ 2 / 2 * v)) :=
          Real.log_le_log hpos (traceExp_cumulantSum_le μ A g hA hSG θ)
      _ = _ := by rw [Real.log_mul hd0.ne' (Real.exp_pos _).ne', Real.log_exp]
  calc (∫ ω, lambdaMax (∑ k, g k ω • A k) ∂μ)
      ≤ Real.log (traceExp (cumulantSum μ (fun k ω => g k ω • A k) θ)) / θ := h1
    _ ≤ (Real.log d + θ ^ 2 / 2 * v) / θ := div_le_div_of_nonneg_right hlog hθ.le
    _ = Real.log d / θ + θ * v / 2 := by field_simp

/-- **Hermitian series, tail bound**: for independent `1`-sub-Gaussian coefficients and Hermitian
`A k`, `P{λmax(∑ k, g k • A k) ≥ t} ≤ gaussianSeriesTail d ‖∑ k, A k ^ 2‖ t` for `t ≥ 0`. Tropp
2015, Thm 4.6.1, eq. (4.6.3).
atlas: matrix-gaussian-series -/
theorem measureReal_lambdaMax_hermitianSeries_ge_le (hA : ∀ k, (A k).IsHermitian)
    (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hSG : ∀ k, HasSubgaussianMGF (g k) 1 μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (∑ k, g k ω • A k)} ≤
      gaussianSeriesTail d (specNorm (∑ k, A k ^ 2)) t := by
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  set v := specNorm (∑ k, A k ^ 2) with hv
  have hv0 : 0 ≤ v := specNorm_nonneg _
  have hT : ∀ θ : ℝ, 0 < θ → ∀ t : ℝ, μ.real {ω | t ≤ lambdaMax (∑ k, g k ω • A k)} ≤
      d * Real.exp (-θ * t + θ ^ 2 / 2 * v) := by
    intro θ hθ t
    obtain ⟨hXMeas, hXHerm, -, hXIndep, hXExp⟩ := master_package μ A g hA hMeas hIndep hSG θ
    have h1 := measureReal_lambdaMax_sum_ge_le_exp_mul_traceExp_cumulantSum μ
      (fun k ω => g k ω • A k) hθ hXMeas hXHerm hXIndep hXExp t
    calc _ ≤ Real.exp (-θ * t) * traceExp (cumulantSum μ (fun k ω => g k ω • A k) θ) := h1
      _ ≤ Real.exp (-θ * t) * (d * Real.exp (θ ^ 2 / 2 * v)) :=
          mul_le_mul_of_nonneg_left (traceExp_cumulantSum_le μ A g hA hSG θ) (Real.exp_pos _).le
      _ = _ := by rw [Real.exp_add]; ring
  have hP1 : ∀ t : ℝ, μ.real {ω | t ≤ lambdaMax (∑ k, g k ω • A k)} ≤ d := fun t =>
    (measureReal_le_one (μ := μ)).trans hd
  unfold gaussianSeriesTail
  split_ifs with hv0' ht0
  · exact hP1 t
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hlin : Tendsto (fun θ : ℝ => -θ * t) atTop atBot := by
      have := (tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.atTop_mul_const htp))
      refine this.congr (fun θ => ?_)
      simp [neg_mul]
    have hlim : Tendsto (fun θ : ℝ => (d : ℝ) * Real.exp (-θ * t + θ ^ 2 / 2 * v)) atTop
        (𝓝 0) := by
      rw [hv0']
      simp only [mul_zero, add_zero]
      simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul (d : ℝ)
    exact ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun θ hθ => hT θ hθ t)
  · have hvp : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hv0')
    rcases ht.eq_or_lt with h0 | htp
    · subst h0
      simpa using hP1 0
    · have h := hT (t / v) (div_pos htp hvp) t
      have e : -(t / v) * t + (t / v) ^ 2 / 2 * v = -(t ^ 2) / (2 * v) := by
        field_simp
        ring
      rwa [e] at h

/-- Hermitian Gaussian series, expectation bound (Tropp 2015, Thm 4.6.1): the sub-Gaussian
theorem for standard Gaussian coefficients. -/
theorem integral_lambdaMax_hermitianSeries_le_of_hasLaw_gaussianReal (hA : ∀ k, (A k).IsHermitian)
    (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hg : ∀ k, HasLaw (g k) (gaussianReal 0 1) μ) :
    (∫ ω, lambdaMax (∑ k, g k ω • A k) ∂μ) ≤
      Real.sqrt (2 * specNorm (∑ k, A k ^ 2) * Real.log d) :=
  integral_lambdaMax_hermitianSeries_le μ A g hA hMeas hIndep
    (fun k => hasSubgaussianMGF_of_hasLaw_gaussianReal (hg k))

/-- Hermitian Gaussian series, tail bound (Tropp 2015, Thm 4.6.1): the sub-Gaussian theorem for
standard Gaussian coefficients. -/
theorem measureReal_lambdaMax_hermitianSeries_ge_le_of_hasLaw_gaussianReal
    (hA : ∀ k, (A k).IsHermitian) (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hg : ∀ k, HasLaw (g k) (gaussianReal 0 1) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (∑ k, g k ω • A k)} ≤
      gaussianSeriesTail d (specNorm (∑ k, A k ^ 2)) t :=
  measureReal_lambdaMax_hermitianSeries_ge_le μ A g hA hMeas hIndep
    (fun k => hasSubgaussianMGF_of_hasLaw_gaussianReal (hg k)) ht

/-- Hermitian Rademacher series, expectation bound (Tropp 2015, Thm 4.6.1): the sub-Gaussian
theorem for Rademacher coefficients. -/
theorem integral_lambdaMax_hermitianSeries_le_of_hasLaw_rademacherMeasure
    (hA : ∀ k, (A k).IsHermitian) (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hg : ∀ k, HasLaw (g k) rademacherMeasure μ) :
    (∫ ω, lambdaMax (∑ k, g k ω • A k) ∂μ) ≤
      Real.sqrt (2 * specNorm (∑ k, A k ^ 2) * Real.log d) :=
  integral_lambdaMax_hermitianSeries_le μ A g hA hMeas hIndep
    (fun k => hasSubgaussianMGF_of_hasLaw_rademacherMeasure (hg k))

/-- Hermitian Rademacher series, tail bound (Tropp 2015, Thm 4.6.1): the sub-Gaussian theorem for
Rademacher coefficients. -/
theorem measureReal_lambdaMax_hermitianSeries_ge_le_of_hasLaw_rademacherMeasure
    (hA : ∀ k, (A k).IsHermitian) (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hg : ∀ k, HasLaw (g k) rademacherMeasure μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (∑ k, g k ω • A k)} ≤
      gaussianSeriesTail d (specNorm (∑ k, A k ^ 2)) t :=
  measureReal_lambdaMax_hermitianSeries_ge_le μ A g hA hMeas hIndep
    (fun k => hasSubgaussianMGF_of_hasLaw_rademacherMeasure (hg k)) ht

end HermitianSeries

end NLAlib
