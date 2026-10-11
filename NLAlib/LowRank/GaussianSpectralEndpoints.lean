import NLAlib.LowRank.SpectralRangeFinder
import NLAlib.Matrix.SpectralMeasurable

/-!
# The one-row Gaussian range-finder endpoint

The Frobenius inverse moment supplies the omitted one-row endpoint of HMT's
spectral pseudoinverse expectation, with its printed spectral constant.
Source: manuscript `sa:expected-power`, endpoint calculation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The one-row Frobenius-moment constant is bounded by the HMT spectral constant.
Source: manuscript `sa:expected-power`, its one-row endpoint calculation. -/
theorem sqrt_one_div_sub_one_le_exp_sqrt_add_one_div {p : ℕ} (hp : 2 ≤ p) :
    Real.sqrt (1 / ((p : ℝ) - 1)) ≤ Real.exp 1 * Real.sqrt (1 + p) / p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hsq : (1 / ((p : ℝ) - 1)) * (p : ℝ) ^ 2 ≤ 4 * (1 + p) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpm]
    nlinarith
  have hs : (Real.sqrt (1 / ((p : ℝ) - 1)) * p) ^ 2 ≤
      (2 * Real.sqrt (1 + (p : ℝ))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    norm_num
    simpa only [one_div] using hsq
  have hle := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt (1 / ((p : ℝ) - 1)) * p)
    (by positivity : 0 ≤ 2 * Real.sqrt (1 + (p : ℝ)))).mp hs
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using Real.add_one_le_exp 1
  apply (le_div_iff₀ hp0).2
  exact hle.trans (mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg _))

/-- The spectral Gaussian inverse expectation with the HMT constant includes one row.
Source: HMT (2011), Proposition 10.2; manuscript `sa:expected-power`.
The one-row case follows from the proved Frobenius inverse moment and Jensen. -/
theorem integrable_and_integral_specNorm_pinvR_gaussianMatrix_le_of_pos
    {k p : ℕ} (hk : 1 ≤ k) (hp : 2 ≤ p) :
    Integrable (fun G : Fin k → Fin (k + p) → ℝ => specNorm (pinvR (Matrix.of G)))
      (gaussianMatrix k (k + p)) ∧
    ∫ G, specNorm (pinvR (Matrix.of G)) ∂gaussianMatrix k (k + p) ≤
      Real.exp 1 * Real.sqrt (k + p) / p := by
  by_cases hk2 : 2 ≤ k
  · obtain ⟨hi, hv⟩ := integrable_and_integral_specNorm_pinvR_gaussianMatrix_le
      (r := k) (k := k + p) hk2 (by omega)
    refine ⟨hi, ?_⟩
    convert hv using 1
    push_cast
    ring
  · have hk1 : k = 1 := by omega
    subst k
    obtain ⟨hFi, hFv⟩ := integrable_and_integral_frobNorm_pinvR_gaussianMatrix_le (k := 1) hp
    have hSi : Integrable (fun G : Fin 1 → Fin (1 + p) → ℝ =>
        specNorm (pinvR (Matrix.of G))) (gaussianMatrix 1 (1 + p)) := by
      refine hFi.mono' (measurable_specNorm_of_entries
        (fun i j => measurable_pinvR_entry i j)).aestronglyMeasurable ?_
      exact ae_of_all _ fun G => by
        rw [Real.norm_of_nonneg (specNorm_nonneg _)]
        exact specNorm_le_frobNorm _
    refine ⟨hSi, ?_⟩
    calc ∫ G, specNorm (pinvR (Matrix.of G)) ∂gaussianMatrix 1 (1 + p) ≤
          ∫ G, frobNorm (pinvR (Matrix.of G)) ∂gaussianMatrix 1 (1 + p) :=
        integral_mono hSi hFi fun G => specNorm_le_frobNorm _
      _ ≤ Real.sqrt (1 / ((p : ℝ) - 1)) := by simpa only [Nat.cast_one] using hFv
      _ ≤ _ := by simpa only [Nat.cast_one] using sqrt_one_div_sub_one_le_exp_sqrt_add_one_div hp

/-- The conditioned Gaussian range-finder bound includes every positive leading rank. Source: HMT (2011), Theorem 10.6; manuscript `sa:expected-power`, one-row endpoint. -/
theorem integrable_and_integral_specNorm_mul_block_mul_pinvR_block_le_of_pos
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {n k p r r' : ℕ} (Ω : Ωs → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n (k + p))
    {V₁ : Matrix (Fin n) (Fin k) ℝ} {V₂ : Matrix (Fin n) (Fin r') ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (S₂ : Matrix (Fin r) (Fin r') ℝ) (hk : 1 ≤ k) (hp : 2 ≤ p) :
    Integrable (fun ω => specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) μ ∧
    ∫ ω, specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ∂μ ≤
      specNorm S₂ * Real.sqrt (k / ((p : ℝ) - 1)) +
        frobNorm S₂ * (Real.exp 1 * Real.sqrt (k + p) / p) := by
  set X : Ωs → Fin k → Fin (k + p) → ℝ :=
    fun ω => Matrix.of.symm (V₁ᵀ * Matrix.of (Matrix.of.symm (Ω ω))) with hXdef
  set Y : Ωs → Fin r' → Fin (k + p) → ℝ :=
    fun ω => Matrix.of.symm (V₂ᵀ * Matrix.of (Matrix.of.symm (Ω ω))) with hYdef
  have hXlaw : μ.map X = gaussianMatrix k (k + p) := map_block_eq_gaussianMatrix hΩ V₁ hV₁
  have hYlaw : μ.map Y = gaussianMatrix r' (k + p) := map_block_eq_gaussianMatrix hΩ V₂ hV₂
  have hind : IndepFun X Y μ := indepFun_block_of_map_eq hΩ V₁ V₂ hV₁ hV₂ hV
  have hXm := aemeasurable_of_map_eq_gaussianMatrix hXlaw
  have hYm := aemeasurable_of_map_eq_gaussianMatrix hYlaw
  set g : (Fin k → Fin (k + p) → ℝ) → (Fin r' → Fin (k + p) → ℝ) → ℝ :=
    fun x y => specNorm (S₂ * Matrix.of y * pinvR (Matrix.of x)) with hgdef
  have hfg : (fun ω => specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) =
      fun ω => g (X ω) (Y ω) := rfl
  have hgm : Measurable fun q : (Fin k → Fin (k + p) → ℝ) × (Fin r' → Fin (k + p) → ℝ) =>
      g q.1 q.2 := by
    refine measurable_specNorm_of_entries fun i j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_
      ((measurable_pinvR_entry l j).comp measurable_fst)
    fun_prop
  -- The deterministic bound after integrating out `Ω₂`.
  set B : (Fin k → Fin (k + p) → ℝ) → ℝ := fun x =>
    specNorm S₂ * frobNorm (pinvR (Matrix.of x)) + frobNorm S₂ * specNorm (pinvR (Matrix.of x))
    with hBdef
  obtain ⟨hFi, hFv⟩ := integrable_and_integral_frobNorm_pinvR_gaussianMatrix_le (k := k) hp
  obtain ⟨hSi, hSv⟩ := integrable_and_integral_specNorm_pinvR_gaussianMatrix_le_of_pos hk hp
  have hBi : Integrable B (gaussianMatrix k (k + p)) :=
    (hFi.const_mul _).add (hSi.const_mul _)
  have hB0 : ∀ x, 0 ≤ B x := fun x =>
    add_nonneg (mul_nonneg (specNorm_nonneg _) (frobNorm_nonneg _))
      (mul_nonneg (frobNorm_nonneg _) (specNorm_nonneg _))
  set bound := specNorm S₂ * Real.sqrt (k / ((p : ℝ) - 1)) +
    frobNorm S₂ * (Real.exp 1 * Real.sqrt (k + p) / p) with hbound
  have hbound0 : 0 ≤ bound :=
    add_nonneg (mul_nonneg (specNorm_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (frobNorm_nonneg _) (by positivity))
  have hBint : ∫ x, B x ∂(gaussianMatrix k (k + p)) ≤ bound := by
    rw [hBdef, integral_add (hFi.const_mul _) (hSi.const_mul _), integral_const_mul,
      integral_const_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hFv (specNorm_nonneg _))
      (mul_le_mul_of_nonneg_left hSv (frobNorm_nonneg _))
  have hL : ∫⁻ ω, ENNReal.ofReal (g (X ω) (Y ω)) ∂μ ≤ ENNReal.ofReal bound := by
    rw [lintegral_of_indepFun hXm hYm hind (g := fun x y => ENNReal.ofReal (g x y))
      (ENNReal.measurable_ofReal.comp hgm).aemeasurable, hXlaw, hYlaw]
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x y) ∂gaussianMatrix r' (k + p) ∂gaussianMatrix k (k + p)
        ≤ ∫⁻ x, ENNReal.ofReal (B x) ∂gaussianMatrix k (k + p) := by
          refine lintegral_mono fun x => ?_
          obtain ⟨hci, hcv⟩ :=
            integrable_and_integral_specNorm_mul_gaussianMatrix_mul_le S₂ (pinvR (Matrix.of x))
          rw [← ofReal_integral_eq_lintegral_ofReal hci (ae_of_all _ fun _ => specNorm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hcv
      _ = ENNReal.ofReal (∫ x, B x ∂gaussianMatrix k (k + p)) :=
          (ofReal_integral_eq_lintegral_ofReal hBi (ae_of_all _ hB0)).symm
      _ ≤ ENNReal.ofReal bound := ENNReal.ofReal_le_ofReal hBint
  have hf0 : 0 ≤ᵐ[μ] fun ω => g (X ω) (Y ω) := ae_of_all _ fun _ => specNorm_nonneg _
  have hfm : AEStronglyMeasurable (fun ω => g (X ω) (Y ω)) μ :=
    (hgm.comp_aemeasurable (hXm.prodMk hYm)).aestronglyMeasurable
  have hfi : Integrable (fun ω => g (X ω) (Y ω)) μ :=
    ⟨hfm, (hasFiniteIntegral_iff_ofReal hf0).2 (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  rw [hfg]
  refine ⟨hfi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hfm]
  exact ENNReal.toReal_le_of_le_ofReal hbound0 hL

/-- The conditioned Gaussian range-finder bound includes every positive leading rank. Source: HMT (2011), Theorem 10.6; manuscript `sa:expected-power`, one-row endpoint. -/
theorem integral_specNorm_residual_le_of_gaussian_of_pos
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {m' q' : Type*} [Fintype m'] [DecidableEq m'] [Fintype q'] [DecidableEq q']
    {n k p r r' : ℕ} {A : Matrix m' (Fin n) ℝ} {U₁ : Matrix m' (Fin k) ℝ}
    {U₂ : Matrix m' (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ} {V₂ : Matrix (Fin n) (Fin r') ℝ}
    {S₁ : Matrix (Fin k) (Fin k) ℝ} {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hk : 1 ≤ k) (hp : 2 ≤ p) (Ω : Ωs → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n (k + p))
    (Q : Ωs → Matrix m' q' ℝ) (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω) :
    ∫ ω, specNorm (residual (Q ω) A) ∂μ ≤
      (1 + Real.sqrt (k / ((p : ℝ) - 1))) * specNorm S₂ +
        Real.exp 1 * Real.sqrt (k + p) / p * frobNorm S₂ := by
  obtain ⟨hint, hle⟩ :=
    integrable_and_integral_specNorm_mul_block_mul_pinvR_block_le_of_pos Ω hΩ hV₁ hV₂ hV S₂ hk hp
  have hunit : ∀ᵐ ω ∂μ, IsUnit ((V₁ᵀ * Ω ω) * (V₁ᵀ * Ω ω)ᵀ) :=
    ae_isUnit_block hΩ V₁ hV₁ (by omega)
  have hpt : (fun ω => specNorm (residual (Q ω) A)) ≤ᵐ[μ]
      fun ω => specNorm S₂ + specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) := by
    filter_upwards [hQo, hQr, hunit] with ω hqo hqr hu
    exact specNorm_residual_le_of_range_subset hA hU₂ hV₁ hV₂ hV rfl rfl hu hqo hqr
  have hmono : ∫ ω, specNorm (residual (Q ω) A) ∂μ ≤
      ∫ ω, (specNorm S₂ + specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ fun ω => specNorm_nonneg _)
      ((integrable_const (specNorm S₂)).add hint) hpt
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul] at hmono
  refine hmono.trans ?_
  have := hle
  nlinarith [specNorm_nonneg S₂, frobNorm_nonneg S₂]

/-- The conditioned Gaussian range-finder bound includes every positive leading rank. Source: HMT (2011), Theorem 10.6; manuscript `sa:expected-power`, one-row endpoint. -/
theorem integral_specNorm_residual_le_singularValues_of_gaussian_of_pos
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {q' : Type*} [Fintype q'] [DecidableEq q'] {m n k p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hk : 1 ≤ k) (hp : 2 ≤ p) (hkn : k ≤ n) (Ω : Ωs → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n (k + p))
    (Q : Ωs → Matrix (Fin m) q' ℝ) (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω) :
    ∫ ω, specNorm (residual (Q ω) A) ∂μ ≤
      (1 + Real.sqrt (k / ((p : ℝ) - 1))) * singularValues A k +
        Real.exp 1 * Real.sqrt (k + p) / p * Real.sqrt (singularValueTailSq A k) := by
  obtain ⟨r, U₁, U₂, V₁, V₂, S₂, hA, hU₂, hV₁, hV₂, hV, hspec, hfrob⟩ :=
    exists_svd_right_blocks_specNorm A k hkn
  have h := integral_specNorm_residual_le_of_gaussian_of_pos hA hU₂ hV₁ hV₂ hV hk hp Ω hΩ Q hQo hQr
  rwa [hspec, frobNorm, hfrob] at h

end NLAlib
