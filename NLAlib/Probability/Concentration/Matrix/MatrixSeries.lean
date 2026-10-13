import NLAlib.Probability.Concentration.Matrix.HermitianSeries
import NLAlib.Probability.Concentration.Matrix.MatrixBernstein
/-!
# Theorem 4.1.1 — Rectangular series with sub-Gaussian coefficients

For `Z = ∑ k, g k • B k` with independent `1`-sub-Gaussian coefficients `g k` (standard Gaussian
or Rademacher coefficients are the corollaries) and `v = max ‖∑ B k B kᴴ‖ ‖∑ B kᴴ B k‖`:

* `rectSecondMoment_matrixSeries_eq`: `rectSecondMoment μ Z = v` when `𝔼 (g k)² = 1`;
* `integral_specNorm_matrixSeries_le`: `𝔼 ‖Z‖ ≤ √(2 v log (m + n))`;
* `measureReal_specNorm_matrixSeries_ge_le`: `P{‖Z‖ ≥ t} ≤ gaussianSeriesTail (m + n) v t`;
* the `…_of_hasLaw_gaussianReal` and `…_of_hasLaw_rademacherMeasure` corollaries.

Atlas: `matrix-gaussian-series`. Source: Tropp 2015, *An Introduction to Matrix Concentration
Inequalities*, Theorem 4.1.1, equations (4.1.2–6), by Hermitian dilation of Theorem 4.6.1.
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder

namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- The second moment of a rectangular series with independent, centred, unit-variance
coefficients. -/
theorem integral_sum_smul_mul_sum_smul_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} {p q r : Type*} [Fintype p] [Fintype q] [Fintype r] [DecidableEq r]
    (g : Fin N → Ω → ℝ) (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (h2 : ∀ k, MemLp (g k) 2 μ) (h0 : ∀ k, ∫ ω, g k ω ∂μ = 0)
    (h1 : ∀ k, ∫ ω, g k ω ^ 2 ∂μ = 1)
    (X : Fin N → Matrix p q ℂ) (Y : Fin N → Matrix q r ℂ) :
    ∫ ω, (∑ j, g j ω • X j) * (∑ k, g k ω • Y k) ∂μ = ∑ k, X k * Y k := by
  have hint : ∀ j k, Integrable (fun ω => g j ω * g k ω) μ := fun j k =>
    (h2 j).integrable_mul (h2 k)
  have hcorr : ∀ j k, ∫ ω, g j ω * g k ω ∂μ = if j = k then 1 else 0 := by
    intro j k
    split_ifs with hjk
    · subst hjk; simpa [sq] using h1 j
    · rw [IndepFun.integral_fun_mul_eq_mul_integral (hIndep.indepFun hjk)
        (hMeas j).aestronglyMeasurable (hMeas k).aestronglyMeasurable, h0 j, zero_mul]
  have e : ∀ ω, (∑ j, g j ω • X j) * (∑ k, g k ω • Y k) =
      ∑ j, ∑ k, (g j ω * g k ω) • (X j * Y k) := by
    intro ω
    rw [Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp_rw [e]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun k _ => (hint j k).smul_const _))]
  have h2' : ∀ j, ∫ ω, ∑ k, (g j ω * g k ω) • (X j * Y k) ∂μ = X j * Y j := by
    intro j
    rw [integral_finsetSum _ (fun k _ => (hint j k).smul_const _)]
    simp_rw [integral_smul_const, hcorr, ite_smul, one_smul, zero_smul]
    simp
  simp_rw [h2']

section MatrixSeries

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m n N : ℕ}
  [NeZero m] [NeZero n] (B : Fin N → Matrix (Fin m) (Fin n) ℂ) (g : Fin N → Ω → ℝ)

open scoped Matrix.Norms.L2Operator in
/-- **Variance of a rectangular series**: for independent centred unit-variance coefficients,
`rectSecondMoment μ (∑ k, g k • B k) = max ‖∑ k, B k * B kᴴ‖ ‖∑ k, B kᴴ * B k‖`. Tropp 2015,
eq. (4.1.3).
atlas: matrix-gaussian-series -/
theorem rectSecondMoment_matrixSeries_eq (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hSG : ∀ k, HasSubgaussianMGF (g k) 1 μ) (hVar : ∀ k, ∫ ω, g k ω ^ 2 ∂μ = 1) :
    rectSecondMoment μ (fun ω => ∑ k, g k ω • B k) =
      max (specNorm (∑ k, B k * (B k)ᴴ)) (specNorm (∑ k, (B k)ᴴ * B k)) := by
  have h2 : ∀ k, MemLp (g k) 2 μ := fun k => (hSG k).memLp 2
  have h0 : ∀ k, ∫ ω, g k ω ∂μ = 0 := fun k => integral_eq_zero_of_hasSubgaussianMGF (hSG k)
  have hZh : ∀ ω, (∑ k, g k ω • B k)ᴴ = ∑ k, g k ω • (B k)ᴴ := by
    intro ω
    simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  unfold rectSecondMoment
  simp_rw [hZh]
  rw [integral_sum_smul_mul_sum_smul_eq μ g hMeas hIndep h2 h0 hVar B (fun k => (B k)ᴴ),
    integral_sum_smul_mul_sum_smul_eq μ g hMeas hIndep h2 h0 hVar (fun k => (B k)ᴴ) B]

/-- The Hermitian dilations of the coefficients, reindexed to `Fin (m + n)`. -/
private def dilationFamily : Fin N → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
  fun k => Matrix.reindex finSumFinEquiv finSumFinEquiv (dilation (B k))

private lemma isHermitian_dilationFamily (k : Fin N) : (dilationFamily B k).IsHermitian :=
  (dilation_identities (B k)).1.submatrix _

private lemma sum_smul_dilationFamily (ω : Ω) :
    ∑ k, g k ω • dilationFamily B k =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (dilation (∑ k, g k ω • B k)) := by
  rw [← Matrix.coe_reindexLinearEquiv ℝ ℂ finSumFinEquiv finSumFinEquiv, ← dilationLinearMap_apply]
  simp only [map_sum, map_smul, dilationFamily, dilationLinearMap_apply,
    Matrix.coe_reindexLinearEquiv]

open scoped Matrix.Norms.L2Operator in
private lemma lambdaMax_sum_smul_dilationFamily (ω : Ω) :
    lambdaMax (∑ k, g k ω • dilationFamily B k) = specNorm (∑ k, g k ω • B k) := by
  rw [sum_smul_dilationFamily, lambdaMax_reindex, specNorm_eq_norm]
  exact (dilation_identities (∑ k, g k ω • B k)).2.2.1.trans
    (dilation_identities (∑ k, g k ω • B k)).2.2.2

open scoped Matrix.Norms.L2Operator in
private lemma specNorm_sum_dilationFamily_sq :
    specNorm (∑ k, dilationFamily B k ^ 2) =
      max (specNorm (∑ k, B k * (B k)ᴴ)) (specNorm (∑ k, (B k)ᴴ * B k)) := by
  have hsq : ∀ k, dilationFamily B k ^ 2 =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (dilation (B k) ^ 2) := by
    intro k
    rw [dilationFamily, ← Matrix.coe_reindexAlgEquiv ℝ, map_pow]
  have hsum : ∑ k, dilation (B k) ^ 2 =
      Matrix.fromBlocks (∑ k, B k * (B k)ᴴ) 0 0 (∑ k, (B k)ᴴ * B k) := by
    simp_rw [dilation_sq]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.sum_apply]
  simp_rw [hsq]
  rw [← Matrix.coe_reindexLinearEquiv ℝ ℂ finSumFinEquiv finSumFinEquiv,
    ← map_sum, hsum]
  simp only [Matrix.reindexLinearEquiv_apply, specNorm_eq_norm, norm_reindex, norm_fromBlocks_diag]

private lemma one_le_card_sum : (1 : ℝ) ≤ ((m + n : ℕ) : ℝ) := by
  have := NeZero.ne m
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)

/-- **Rectangular series, expectation bound**: for independent `1`-sub-Gaussian coefficients,
`𝔼 ‖∑ k, g k • B k‖ ≤ √(2 v log (m + n))` with `v = max ‖∑ B k B kᴴ‖ ‖∑ B kᴴ B k‖`. Tropp 2015,
Thm 4.1.1, eq. (4.1.4).
atlas: matrix-gaussian-series -/
theorem integral_specNorm_matrixSeries_le (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hSG : ∀ k, HasSubgaussianMGF (g k) 1 μ) :
    (∫ ω, specNorm (∑ k, g k ω • B k) ∂μ) ≤
      Real.sqrt (2 * max (specNorm (∑ k, B k * (B k)ᴴ)) (specNorm (∑ k, (B k)ᴴ * B k)) *
        Real.log (m + n)) := by
  have : NeZero (m + n) := ⟨by have := NeZero.ne m; omega⟩
  have H := integral_lambdaMax_hermitianSeries_le μ (dilationFamily B) g
    (isHermitian_dilationFamily B) hMeas hIndep hSG
  simp only [lambdaMax_sum_smul_dilationFamily, specNorm_sum_dilationFamily_sq] at H
  simpa [Nat.cast_add] using H

/-- **Rectangular series, tail bound**: for independent `1`-sub-Gaussian coefficients and
`t ≥ 0`, `P{‖∑ k, g k • B k‖ ≥ t} ≤ gaussianSeriesTail (m + n) v t`. Tropp 2015, Thm 4.1.1,
eq. (4.1.5).
atlas: matrix-gaussian-series -/
theorem measureReal_specNorm_matrixSeries_ge_le (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ) (hSG : ∀ k, HasSubgaussianMGF (g k) 1 μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, g k ω • B k)} ≤
      gaussianSeriesTail (m + n)
        (max (specNorm (∑ k, B k * (B k)ᴴ)) (specNorm (∑ k, (B k)ᴴ * B k))) t := by
  have : NeZero (m + n) := ⟨by have := NeZero.ne m; omega⟩
  have H := measureReal_lambdaMax_hermitianSeries_ge_le μ (dilationFamily B) g
    (isHermitian_dilationFamily B) hMeas hIndep hSG ht
  simpa only [lambdaMax_sum_smul_dilationFamily, specNorm_sum_dilationFamily_sq] using H

/-- Rectangular Gaussian series, expectation bound (Tropp 2015, Thm 4.1.1). -/
theorem integral_specNorm_matrixSeries_le_of_hasLaw_gaussianReal (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ) (hg : ∀ k, HasLaw (g k) (gaussianReal 0 1) μ) :
    (∫ ω, specNorm (∑ k, g k ω • B k) ∂μ) ≤
      Real.sqrt (2 * max (specNorm (∑ k, B k * (B k)ᴴ)) (specNorm (∑ k, (B k)ᴴ * B k)) *
        Real.log (m + n)) :=
  integral_specNorm_matrixSeries_le μ B g hMeas hIndep
    (fun k => hasSubgaussianMGF_of_hasLaw_gaussianReal (hg k))

/-- Rectangular Gaussian series, tail bound (Tropp 2015, Thm 4.1.1). -/
theorem measureReal_specNorm_matrixSeries_ge_le_of_hasLaw_gaussianReal
    (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hg : ∀ k, HasLaw (g k) (gaussianReal 0 1) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, g k ω • B k)} ≤
      gaussianSeriesTail (m + n)
        (max (specNorm (∑ k, B k * (B k)ᴴ)) (specNorm (∑ k, (B k)ᴴ * B k))) t :=
  measureReal_specNorm_matrixSeries_ge_le μ B g hMeas hIndep
    (fun k => hasSubgaussianMGF_of_hasLaw_gaussianReal (hg k)) ht

/-- Rectangular Rademacher series, expectation bound (Tropp 2015, Thm 4.1.1). -/
theorem integral_specNorm_matrixSeries_le_of_hasLaw_rademacherMeasure
    (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hg : ∀ k, HasLaw (g k) rademacherMeasure μ) :
    (∫ ω, specNorm (∑ k, g k ω • B k) ∂μ) ≤
      Real.sqrt (2 * max (specNorm (∑ k, B k * (B k)ᴴ)) (specNorm (∑ k, (B k)ᴴ * B k)) *
        Real.log (m + n)) :=
  integral_specNorm_matrixSeries_le μ B g hMeas hIndep
    (fun k => hasSubgaussianMGF_of_hasLaw_rademacherMeasure (hg k))

/-- Rectangular Rademacher series, tail bound (Tropp 2015, Thm 4.1.1). -/
theorem measureReal_specNorm_matrixSeries_ge_le_of_hasLaw_rademacherMeasure
    (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (hg : ∀ k, HasLaw (g k) rademacherMeasure μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, g k ω • B k)} ≤
      gaussianSeriesTail (m + n)
        (max (specNorm (∑ k, B k * (B k)ᴴ)) (specNorm (∑ k, (B k)ᴴ * B k))) t :=
  measureReal_specNorm_matrixSeries_ge_le μ B g hMeas hIndep
    (fun k => hasSubgaussianMGF_of_hasLaw_rademacherMeasure (hg k)) ht

end MatrixSeries

end NLAlib
