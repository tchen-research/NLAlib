import NLAlib.Probability.SubGaussian.ExpSquare

/-!
# Centred squares and products of sub-Gaussian variables

For `ProbabilityTheory.HasSubgaussianMGF X c μ` and a real proxy `C₀ ≥ c`, `C₀ > 0`:

* `integral_exp_centered_sq_le_exp_quadratic_{nonneg,nonpos}`,
  `centered_sq_cgf_le_of_hasSubgaussianMGF_of_le`: the centred square `X² - 𝔼 X²` has a local
  quadratic MGF / CGF bound `2e (θ C₀ e)²` for `|θ| C₀ e ≤ 1/2`;
* `integral_exp_mul_prod_le_of_indepFun_hasSubgaussianMGF_of_le`: for independent sub-Gaussian
  `X`, `Y`, `𝔼 e^{θ X Y} ≤ e^{e² C₀² θ²}` in the same range (and the integrability statements);
* `cgf_const_mul`, `iIndepFun_centered_sq`: bookkeeping for sums of centred squares.

Vershynin 2018, Lemma 2.7.6 and §6.2 (diagonal and decoupled steps of Hanson–Wright). Ported from
HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae (Hanson–Wright proof, Apache-2.0,
authors Yuanhe Zhang, Jason D. Lee, Fanghui Liu); atlas `hanson-wright` (helpers).
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Centred squares -/

/-- MGF of a centred square at a nonnegative parameter:
`𝔼 e^{θ (X² - 𝔼 X²)} ≤ e^{2e (θ C₀ e)²}` for `0 ≤ θ`, `θ C₀ e ≤ 1/2`. Atlas `hanson-wright`
(helper). -/
theorem integral_exp_centered_sq_le_exp_quadratic_nonneg {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_half : θ * C0 * exp 1 ≤ 1 / 2) :
    ∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ ≤
      exp (2 * exp 1 * (θ * C0 * exp 1) ^ 2) := by
  set m : ℝ := ∫ ω, X ω ^ 2 ∂μ with hm_def
  set r : ℝ := θ * C0 * exp 1 with hr_def
  have hm_nonneg : 0 ≤ m := by
    rw [hm_def]
    exact integral_nonneg_of_ae (ae_of_all _ fun ω => sq_nonneg (X ω))
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  have hr_half : r ≤ 1 / 2 := by simpa only [hr_def] using hθ_half
  have hr_lt : r < 1 := by linarith
  have hsmall : θ * C0 * exp 1 < 1 := by simpa only [hr_def] using hr_lt
  have hbase :=
    integral_exp_mul_sq_le_one_add_linear_add_tail_of_hasSubgaussianMGF_of_le h hθ
      hC0 hc_le hsmall
  have hcenter :
      ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ =
        exp (-θ * m) * ∫ ω, exp (θ * X ω ^ 2) ∂μ := by
    calc
      ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ
          = ∫ ω, exp (-θ * m) * exp (θ * X ω ^ 2) ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            rw [← exp_add]
            congr 1
            ring
      _ = exp (-θ * m) * ∫ ω, exp (θ * X ω ^ 2) ∂μ := by
            rw [integral_const_mul]
  have htail_nonneg :
      0 ≤ exp 1 * (r ^ 2 * (1 - r)⁻¹) := by
    have hden_pos : 0 < 1 - r := by linarith
    positivity
  have hmul_base :
      exp (-θ * m) * ∫ ω, exp (θ * X ω ^ 2) ∂μ ≤
        exp (-θ * m) *
          (1 + θ * m + exp 1 * (r ^ 2 * (1 - r)⁻¹)) := by
    rw [← hm_def] at hbase
    exact mul_le_mul_of_nonneg_left hbase (exp_nonneg _)
  have hmain :
      exp (-θ * m) *
          (1 + θ * m + exp 1 * (r ^ 2 * (1 - r)⁻¹))
        ≤ 1 + exp 1 * (r ^ 2 * (1 - r)⁻¹) := by
    have hexp_le_one : exp (-θ * m) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hθ, hm_nonneg]
    have htail_mul :
        exp (-θ * m) * (exp 1 * (r ^ 2 * (1 - r)⁻¹)) ≤
          exp 1 * (r ^ 2 * (1 - r)⁻¹) := by
      calc
        exp (-θ * m) * (exp 1 * (r ^ 2 * (1 - r)⁻¹))
            ≤ 1 * (exp 1 * (r ^ 2 * (1 - r)⁻¹)) := by
              exact mul_le_mul_of_nonneg_right hexp_le_one htail_nonneg
        _ = exp 1 * (r ^ 2 * (1 - r)⁻¹) := by ring
    calc
      exp (-θ * m) *
          (1 + θ * m + exp 1 * (r ^ 2 * (1 - r)⁻¹))
          = exp (-(θ * m)) * (1 + θ * m) +
              exp (-θ * m) * (exp 1 * (r ^ 2 * (1 - r)⁻¹)) := by ring_nf
      _ ≤ 1 + exp 1 * (r ^ 2 * (1 - r)⁻¹) :=
          add_le_add (exp_neg_mul_one_add_le_one (θ * m)) htail_mul
  have htail_le :
      exp 1 * (r ^ 2 * (1 - r)⁻¹) ≤ 2 * exp 1 * r ^ 2 := by
    have hden_pos : 0 < 1 - r := by linarith
    have hinv_le : (1 - r)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hden_pos two_pos]
      linarith
    have hmul : r ^ 2 * (1 - r)⁻¹ ≤ r ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left hinv_le (sq_nonneg r)
    calc
      exp 1 * (r ^ 2 * (1 - r)⁻¹) ≤ exp 1 * (r ^ 2 * 2) :=
        mul_le_mul_of_nonneg_left hmul (exp_pos 1).le
      _ = 2 * exp 1 * r ^ 2 := by ring
  calc
    ∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ
        = ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ := by rw [hm_def]
    _ = exp (-θ * m) * ∫ ω, exp (θ * X ω ^ 2) ∂μ := hcenter
    _ ≤ exp (-θ * m) *
          (1 + θ * m + exp 1 * (r ^ 2 * (1 - r)⁻¹)) := hmul_base
    _ ≤ 1 + exp 1 * (r ^ 2 * (1 - r)⁻¹) := hmain
    _ ≤ 1 + 2 * exp 1 * r ^ 2 := by linarith
    _ ≤ exp (2 * exp 1 * r ^ 2) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * exp 1 * r ^ 2)
    _ = exp (2 * exp 1 * (θ * C0 * exp 1) ^ 2) := by rw [hr_def]

/-- MGF of a centred square at a nonpositive parameter:
`𝔼 e^{θ (X² - 𝔼 X²)} ≤ e^{2e (-θ C₀ e)²}` for `θ ≤ 0` (no smallness needed). Atlas
`hanson-wright` (helper). -/
theorem integral_exp_centered_sq_le_exp_quadratic_nonpos {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : θ ≤ 0)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0) :
    ∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ ≤
      exp (2 * exp 1 * ((-θ) * C0 * exp 1) ^ 2) := by
  set a : ℝ := -θ with ha_def
  set m : ℝ := ∫ ω, X ω ^ 2 ∂μ with hm_def
  set M4 : ℝ := ∫ ω, X ω ^ 4 ∂μ with hM4_def
  have ha_nonneg : 0 ≤ a := by rw [ha_def]; linarith
  have hX2_int : Integrable (fun ω => X ω ^ 2) μ := by
    exact integrable_pow_of_integrable_exp_mul
      (X := X) (t := 1) one_ne_zero
      (h.integrable_exp_mul 1)
      (h.integrable_exp_mul (-1)) 2
  have hX4_int : Integrable (fun ω => X ω ^ 4) μ := by
    exact integrable_pow_of_integrable_exp_mul
      (X := X) (t := 1) one_ne_zero
      (h.integrable_exp_mul 1)
      (h.integrable_exp_mul (-1)) 4
  have hneg_int : Integrable (fun ω => exp (-a * X ω ^ 2)) μ := by
    exact Integrable.of_bound
      ((hX2_int.aemeasurable.const_mul (-a)).exp.aestronglyMeasurable) 1 (by
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha_nonneg) (sq_nonneg (X ω)))
  have hpoly_int :
      Integrable (fun ω => 1 - a * X ω ^ 2 + a ^ 2 * X ω ^ 4) μ :=
    ((integrable_const 1).sub (hX2_int.const_mul a)).add (hX4_int.const_mul (a ^ 2))
  have hneg_bound :
      ∫ ω, exp (-a * X ω ^ 2) ∂μ ≤ 1 - a * m + a ^ 2 * M4 := by
    have hpoint :
        (fun ω => exp (-a * X ω ^ 2)) ≤ᵐ[μ]
          fun ω => 1 - a * X ω ^ 2 + a ^ 2 * X ω ^ 4 := by
      filter_upwards with ω
      have hbasic := exp_neg_le_one_sub_add_sq
        (mul_nonneg ha_nonneg (sq_nonneg (X ω)))
      calc
        exp (-a * X ω ^ 2) = exp (-(a * X ω ^ 2)) := by ring_nf
        _ ≤ 1 - (a * X ω ^ 2) + (a * X ω ^ 2) ^ 2 := hbasic
        _ = 1 - a * X ω ^ 2 + a ^ 2 * X ω ^ 4 := by ring_nf
    calc
      ∫ ω, exp (-a * X ω ^ 2) ∂μ
          ≤ ∫ ω, 1 - a * X ω ^ 2 + a ^ 2 * X ω ^ 4 ∂μ :=
            integral_mono_ae hneg_int hpoly_int hpoint
      _ = 1 - a * m + a ^ 2 * M4 := by
        calc
          ∫ ω, 1 - a * X ω ^ 2 + a ^ 2 * X ω ^ 4 ∂μ
              = ∫ ω, (1 - a * X ω ^ 2) + a ^ 2 * X ω ^ 4 ∂μ := by rfl
          _ = ∫ ω, 1 - a * X ω ^ 2 ∂μ + ∫ ω, a ^ 2 * X ω ^ 4 ∂μ := by
              rw [show (fun ω => (1 - a * X ω ^ 2) + a ^ 2 * X ω ^ 4) =
                (fun ω => 1 - a * X ω ^ 2) + (fun ω => a ^ 2 * X ω ^ 4) by
                rfl]
              exact integral_add ((integrable_const 1).sub (hX2_int.const_mul a))
                (hX4_int.const_mul (a ^ 2))
          _ = (1 - a * m) + a ^ 2 * M4 := by
              rw [integral_sub (integrable_const 1) (hX2_int.const_mul a)]
              rw [integral_const_mul, integral_const_mul]
              rw [hm_def, hM4_def]
              simp only [integral_const, probReal_univ, one_smul]
          _ = 1 - a * m + a ^ 2 * M4 := by ring_nf
  have hcenter :
      ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ =
        exp (a * m) * ∫ ω, exp (-a * X ω ^ 2) ∂μ := by
    calc
      ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ
          = ∫ ω, exp (a * m) * exp (-a * X ω ^ 2) ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            rw [← exp_add]
            congr 1
            rw [ha_def]
            ring_nf
      _ = exp (a * m) * ∫ ω, exp (-a * X ω ^ 2) ∂μ := by
            rw [integral_const_mul]
  have hM4_bound : M4 ≤ 2 * exp 1 * (C0 * exp 1) ^ 2 := by
    rw [hM4_def]
    exact integral_pow_four_le_of_hasSubgaussianMGF_of_le h hC0 hc_le
  have hmgf_le_exp_M4 :
      exp (a * m) * ∫ ω, exp (-a * X ω ^ 2) ∂μ ≤ exp (a ^ 2 * M4) := by
    calc
      exp (a * m) * ∫ ω, exp (-a * X ω ^ 2) ∂μ
          ≤ exp (a * m) * (1 - a * m + a ^ 2 * M4) := by
            exact mul_le_mul_of_nonneg_left hneg_bound (exp_nonneg _)
      _ ≤ exp (a * m) * exp (-a * m + a ^ 2 * M4) := by
            exact mul_le_mul_of_nonneg_left
              (by linarith [Real.add_one_le_exp (-a * m + a ^ 2 * M4)])
              (exp_nonneg _)
      _ = exp (a ^ 2 * M4) := by
            rw [← exp_add]
            ring_nf
  have hquad_le :
      a ^ 2 * M4 ≤ a ^ 2 * (2 * exp 1 * (C0 * exp 1) ^ 2) :=
    mul_le_mul_of_nonneg_left hM4_bound (sq_nonneg a)
  calc
    ∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ
        = ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ := by rw [hm_def]
    _ = exp (a * m) * ∫ ω, exp (-a * X ω ^ 2) ∂μ := hcenter
    _ ≤ exp (a ^ 2 * M4) := hmgf_le_exp_M4
    _ ≤ exp (a ^ 2 * (2 * exp 1 * (C0 * exp 1) ^ 2)) :=
        exp_le_exp.mpr hquad_le
    _ = exp (2 * exp 1 * ((-θ) * C0 * exp 1) ^ 2) := by
        rw [ha_def]
        ring_nf

/-- Local exponential integrability of a centred square: `e^{θ (X² - 𝔼 X²)}` is integrable for
`|θ| C₀ e < 1`. Atlas `hanson-wright` (helper). -/
theorem integrable_exp_centered_sq_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ}
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_abs : |θ| * C0 * exp 1 < 1) :
    Integrable (fun ω => exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ))) μ := by
  set m : ℝ := ∫ ω, X ω ^ 2 ∂μ with hm_def
  rcases le_total 0 θ with hθ_nonneg | hθ_nonpos
  · have hsmall : θ * C0 * exp 1 < 1 := by
      simpa [abs_of_nonneg hθ_nonneg] using hθ_abs
    have hsq_int :=
      integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le h hθ_nonneg hC0 hc_le hsmall
    convert hsq_int.const_mul (exp (-θ * m)) using 1
    ext ω
    rw [← exp_add]
    rw [hm_def]
    ring_nf
  · set a : ℝ := -θ with ha_def
    have ha_nonneg : 0 ≤ a := by rw [ha_def]; linarith
    have hX2_int : Integrable (fun ω => X ω ^ 2) μ := by
      exact integrable_pow_of_integrable_exp_mul
        (X := X) (t := 1) one_ne_zero
        (h.integrable_exp_mul 1)
        (h.integrable_exp_mul (-1)) 2
    have hneg_int : Integrable (fun ω => exp (-a * X ω ^ 2)) μ := by
      exact Integrable.of_bound
        ((hX2_int.aemeasurable.const_mul (-a)).exp.aestronglyMeasurable) 1 (by
          filter_upwards with ω
          rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha_nonneg) (sq_nonneg (X ω)))
    convert hneg_int.const_mul (exp (a * m)) using 1
    ext ω
    rw [← exp_add]
    rw [hm_def, ha_def]
    ring_nf

/-- CGF of a centred square: `cgf (X² - 𝔼 X²) θ ≤ 2e (θ C₀ e)²` for `|θ| C₀ e ≤ 1/2`.
Vershynin 2018, Lemma 2.7.6 (sub-exponentiality of `X² - 𝔼 X²`); atlas `hanson-wright`
(helper). -/
theorem centered_sq_cgf_le_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ}
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_abs : |θ| * C0 * exp 1 ≤ 1 / 2) :
    cgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ ≤
      2 * exp 1 * (θ * C0 * exp 1) ^ 2 := by
  have hθ_abs_lt : |θ| * C0 * exp 1 < 1 := by
    linarith
  have hint := integrable_exp_centered_sq_of_hasSubgaussianMGF_of_le h hC0 hc_le hθ_abs_lt
  have hmgf_pos :
      0 < mgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ :=
    mgf_pos hint
  have hmgf_le :
      mgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ ≤
        exp (2 * exp 1 * (θ * C0 * exp 1) ^ 2) := by
    rcases le_total 0 θ with hθ_nonneg | hθ_nonpos
    · have hhalf : θ * C0 * exp 1 ≤ 1 / 2 := by
        rw [abs_of_nonneg hθ_nonneg] at hθ_abs
        exact hθ_abs
      change (∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ) ≤ _
      exact integral_exp_centered_sq_le_exp_quadratic_nonneg h hθ_nonneg hC0 hc_le hhalf
    · have hbound :=
        integral_exp_centered_sq_le_exp_quadratic_nonpos h hθ_nonpos hC0 hc_le
      calc
        mgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ
            ≤ exp (2 * exp 1 * ((-θ) * C0 * exp 1) ^ 2) := by
              change (∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ) ≤ _
              exact hbound
        _ = exp (2 * exp 1 * (θ * C0 * exp 1) ^ 2) := by ring_nf
  calc
    cgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ
        = log (mgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ) := rfl
    _ ≤ log (exp (2 * exp 1 * (θ * C0 * exp 1) ^ 2)) :=
        log_le_log hmgf_pos hmgf_le
    _ = 2 * exp 1 * (θ * C0 * exp 1) ^ 2 := by rw [log_exp]

/-- Scaling inside the CGF: `cgf (a • Y) θ = cgf Y (a θ)`. Atlas `hanson-wright` (helper). -/
theorem cgf_const_mul {μ : Measure Ω} {Y : Ω → ℝ} (a θ : ℝ) :
    cgf (fun ω => a * Y ω) μ θ = cgf Y μ (a * θ) := by
  rw [cgf, cgf, mgf_const_mul]

/-- Centring the squares of independent variables keeps them independent. Atlas
`hanson-wright` (helper). -/
theorem iIndepFun_centered_sq {μ : Measure Ω} {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) :
    iIndepFun (fun i => fun ω => X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂μ) μ := by
  simpa only [Function.comp_def] using
    h_indep.comp
      (fun i x => x ^ 2 - ∫ ω, X i ω ^ 2 ∂μ)
      (fun _ => by fun_prop)

/-! ### Products of independent sub-Gaussian variables -/

/-- For sub-Gaussian laws `νX`, `νY` on `ℝ` (proxies `≤ C₀`), `(y, x) ↦ e^{θ x y}` is integrable
for the product law `νY ⊗ νX` when `(C₀ θ²/2) C₀ e ≤ 1/2`. Atlas `hanson-wright` (helper). -/
theorem integrable_exp_mul_snd_fst_prod_of_hasSubgaussianMGF_of_le
    {νX νY : Measure ℝ} [IsProbabilityMeasure νX] [IsProbabilityMeasure νY]
    {cX cY : ℝ≥0} (hX : HasSubgaussianMGF id cX νX)
    (hY : HasSubgaussianMGF id cY νY) {C0 θ : ℝ}
    (hC0 : 0 < C0) (hcX : (cX : ℝ) ≤ C0) (hcY : (cY : ℝ) ≤ C0)
    (hθ_half : (C0 * θ ^ 2 / 2) * C0 * exp 1 ≤ 1 / 2) :
    Integrable (fun p : ℝ × ℝ => exp (θ * p.2 * p.1)) (νY.prod νX) := by
  let f : ℝ × ℝ → ℝ := fun p => exp (θ * p.2 * p.1)
  have hf_aesm : AEStronglyMeasurable f (νY.prod νX) := by
    dsimp [f]
    fun_prop
  rw [integrable_prod_iff hf_aesm]
  constructor
  · filter_upwards with y
    have hinner := hX.integrable_exp_mul (θ * y)
    convert hinner using 1
    ext x
    dsimp [f]
    ring_nf
  · have hθ2_nonneg : 0 ≤ C0 * θ ^ 2 / 2 := by positivity
    have hbound_int :
        Integrable (fun y : ℝ => exp ((C0 * θ ^ 2 / 2) * y ^ 2)) νY :=
      integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le hY hθ2_nonneg hC0 hcY (by
        linarith [hθ_half])
    refine Integrable.mono' hbound_int ?_ ?_
    · exact hf_aesm.norm.integral_prod_right'
    · filter_upwards with y
      have hinner_eq :
          ∫ x, ‖f (y, x)‖ ∂νX = mgf id νX (θ * y) := by
        unfold mgf
        apply integral_congr_ae
        filter_upwards with x
        dsimp [f]
        rw [abs_of_nonneg (exp_nonneg _)]
        ring_nf
      have hmgf := hX.mgf_le (θ * y)
      have hquad_le :
          (cX : ℝ) * (θ * y) ^ 2 / 2 ≤ C0 * θ ^ 2 * y ^ 2 / 2 := by
        have hnonneg : 0 ≤ (θ * y) ^ 2 / 2 := by positivity
        calc
          (cX : ℝ) * (θ * y) ^ 2 / 2 =
              (cX : ℝ) * ((θ * y) ^ 2 / 2) := by ring_nf
          _ ≤ C0 * ((θ * y) ^ 2 / 2) := mul_le_mul_of_nonneg_right hcX hnonneg
          _ = C0 * θ ^ 2 * y ^ 2 / 2 := by ring_nf
      have hle :
          ∫ x, ‖f (y, x)‖ ∂νX ≤ exp ((C0 * θ ^ 2 / 2) * y ^ 2) := by
        rw [hinner_eq]
        calc
          mgf id νX (θ * y) ≤ exp ((cX : ℝ) * (θ * y) ^ 2 / 2) := hmgf
          _ ≤ exp (C0 * θ ^ 2 * y ^ 2 / 2) := exp_le_exp.mpr hquad_le
          _ = exp ((C0 * θ ^ 2 / 2) * y ^ 2) := by ring_nf
      rw [Real.norm_eq_abs, abs_of_nonneg ?_]
      · exact hle
      · exact integral_nonneg fun x => norm_nonneg _

/-- For sub-Gaussian laws `νX`, `νY` on `ℝ` (proxies `≤ C₀`),
`∫ e^{θ x y} d(νY ⊗ νX) ≤ e^{e² C₀² θ²}` when `(C₀ θ²/2) C₀ e ≤ 1/2`. Atlas `hanson-wright`
(helper). -/
theorem integral_exp_mul_snd_fst_prod_le_of_hasSubgaussianMGF_of_le
    {νX νY : Measure ℝ} [IsProbabilityMeasure νX] [IsProbabilityMeasure νY]
    {cX cY : ℝ≥0} (hX : HasSubgaussianMGF id cX νX)
    (hY : HasSubgaussianMGF id cY νY) {C0 θ : ℝ}
    (hC0 : 0 < C0) (hcX : (cX : ℝ) ≤ C0) (hcY : (cY : ℝ) ≤ C0)
    (hθ_half : (C0 * θ ^ 2 / 2) * C0 * exp 1 ≤ 1 / 2) :
    ∫ p : ℝ × ℝ, exp (θ * p.2 * p.1) ∂(νY.prod νX) ≤
      exp (exp 1 ^ 2 * C0 ^ 2 * θ ^ 2) := by
  let f : ℝ × ℝ → ℝ := fun p => exp (θ * p.2 * p.1)
  have hf_int :
      Integrable f (νY.prod νX) :=
    integrable_exp_mul_snd_fst_prod_of_hasSubgaussianMGF_of_le
      hX hY hC0 hcX hcY hθ_half
  have hθ2_nonneg : 0 ≤ C0 * θ ^ 2 / 2 := by positivity
  have hbound_int :
      Integrable (fun y : ℝ => exp ((C0 * θ ^ 2 / 2) * y ^ 2)) νY :=
    integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le hY hθ2_nonneg hC0 hcY (by
      linarith [hθ_half])
  have houter_bound :
      (fun y : ℝ => ∫ x, f (y, x) ∂νX) ≤ᵐ[νY]
        fun y : ℝ => exp ((C0 * θ ^ 2 / 2) * y ^ 2) := by
    filter_upwards with y
    have hinner_eq :
        ∫ x, f (y, x) ∂νX = mgf id νX (θ * y) := by
      unfold mgf
      apply integral_congr_ae
      filter_upwards with x
      dsimp [f]
      ring_nf
    have hmgf := hX.mgf_le (θ * y)
    have hquad_le :
        (cX : ℝ) * (θ * y) ^ 2 / 2 ≤ C0 * θ ^ 2 * y ^ 2 / 2 := by
      have hnonneg : 0 ≤ (θ * y) ^ 2 / 2 := by positivity
      calc
        (cX : ℝ) * (θ * y) ^ 2 / 2 =
            (cX : ℝ) * ((θ * y) ^ 2 / 2) := by ring_nf
        _ ≤ C0 * ((θ * y) ^ 2 / 2) := mul_le_mul_of_nonneg_right hcX hnonneg
        _ = C0 * θ ^ 2 * y ^ 2 / 2 := by ring_nf
    rw [hinner_eq]
    calc
      mgf id νX (θ * y) ≤ exp ((cX : ℝ) * (θ * y) ^ 2 / 2) := hmgf
      _ ≤ exp (C0 * θ ^ 2 * y ^ 2 / 2) := exp_le_exp.mpr hquad_le
      _ = exp ((C0 * θ ^ 2 / 2) * y ^ 2) := by ring_nf
  calc
    ∫ p : ℝ × ℝ, exp (θ * p.2 * p.1) ∂(νY.prod νX)
        = ∫ y, ∫ x, f (y, x) ∂νX ∂νY := by
          rw [integral_prod f hf_int]
    _ ≤ ∫ y, exp ((C0 * θ ^ 2 / 2) * y ^ 2) ∂νY := by
          exact integral_mono_ae hf_int.integral_prod_left hbound_int houter_bound
    _ ≤ exp (2 * exp 1 * ((C0 * θ ^ 2 / 2) * C0 * exp 1)) :=
          integral_exp_mul_sq_le_exp_linear_of_hasSubgaussianMGF_of_le
            hY hθ2_nonneg hC0 hcY hθ_half
    _ = exp (exp 1 ^ 2 * C0 ^ 2 * θ ^ 2) := by
          congr 1
          ring_nf

/-- For independent sub-Gaussian `X`, `Y` (proxies `≤ C₀`), `e^{θ X Y}` is integrable when
`(C₀ θ²/2) C₀ e ≤ 1/2`. Atlas `hanson-wright` (helper). -/
theorem integrable_exp_mul_prod_of_indepFun_hasSubgaussianMGF_of_le
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (h_indep : X ⟂ᵢ[μ] Y)
    {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) {C0 θ : ℝ}
    (hC0 : 0 < C0) (hcX : (cX : ℝ) ≤ C0) (hcY : (cY : ℝ) ≤ C0)
    (hθ_half : (C0 * θ ^ 2 / 2) * C0 * exp 1 ≤ 1 / 2) :
    Integrable (fun ω => exp (θ * X ω * Y ω)) μ := by
  let φ : Ω → ℝ × ℝ := fun ω => (Y ω, X ω)
  let g : ℝ × ℝ → ℝ := fun p => exp (θ * p.2 * p.1)
  have hφ : AEMeasurable φ μ :=
    (hY.aestronglyMeasurable.prodMk hX.aestronglyMeasurable).aemeasurable
  have hg : AEStronglyMeasurable g (μ.map φ) := by
    dsimp [g]
    fun_prop
  have : IsProbabilityMeasure (μ.map X) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map Y) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hY.aemeasurable
  have hprod_int :
      Integrable g ((μ.map Y).prod (μ.map X)) :=
    integrable_exp_mul_snd_fst_prod_of_hasSubgaussianMGF_of_le
      (νX := μ.map X) (νY := μ.map Y)
      ((HasSubgaussianMGF.id_map_iff hX.aemeasurable).2 hX)
      ((HasSubgaussianMGF.id_map_iff hY.aemeasurable).2 hY)
      hC0 hcX hcY hθ_half
  have hmap_eq :
      μ.map φ = (μ.map Y).prod (μ.map X) := by
    simpa [φ] using
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hY.aemeasurable hX.aemeasurable).mp h_indep.symm
  have hmap_int : Integrable g (μ.map φ) := by
    rwa [hmap_eq]
  have hcomp := (integrable_map_measure hg hφ).1 hmap_int
  convert hcomp using 1
  rfl

/-- For independent sub-Gaussian `X`, `Y` (proxies `≤ C₀`), `𝔼 e^{θ X Y} ≤ e^{e² C₀² θ²}` when
`(C₀ θ²/2) C₀ e ≤ 1/2`. Vershynin 2018, §6.2 (decoupled step); atlas `hanson-wright` (helper). -/
theorem integral_exp_mul_prod_le_of_indepFun_hasSubgaussianMGF_of_le
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (h_indep : X ⟂ᵢ[μ] Y)
    {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) {C0 θ : ℝ}
    (hC0 : 0 < C0) (hcX : (cX : ℝ) ≤ C0) (hcY : (cY : ℝ) ≤ C0)
    (hθ_half : (C0 * θ ^ 2 / 2) * C0 * exp 1 ≤ 1 / 2) :
    ∫ ω, exp (θ * X ω * Y ω) ∂μ ≤ exp (exp 1 ^ 2 * C0 ^ 2 * θ ^ 2) := by
  let φ : Ω → ℝ × ℝ := fun ω => (Y ω, X ω)
  let g : ℝ × ℝ → ℝ := fun p => exp (θ * p.2 * p.1)
  have hφ : AEMeasurable φ μ :=
    (hY.aestronglyMeasurable.prodMk hX.aestronglyMeasurable).aemeasurable
  have hg : AEStronglyMeasurable g (μ.map φ) := by
    dsimp [g]
    fun_prop
  have : IsProbabilityMeasure (μ.map X) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map Y) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hY.aemeasurable
  have hmap_eq :
      μ.map φ = (μ.map Y).prod (μ.map X) := by
    simpa [φ] using
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hY.aemeasurable hX.aemeasurable).mp h_indep.symm
  have hprod_bound :
      ∫ p : ℝ × ℝ, g p ∂((μ.map Y).prod (μ.map X)) ≤
        exp (exp 1 ^ 2 * C0 ^ 2 * θ ^ 2) :=
    integral_exp_mul_snd_fst_prod_le_of_hasSubgaussianMGF_of_le
      (νX := μ.map X) (νY := μ.map Y)
      ((HasSubgaussianMGF.id_map_iff hX.aemeasurable).2 hX)
      ((HasSubgaussianMGF.id_map_iff hY.aemeasurable).2 hY)
      hC0 hcX hcY hθ_half
  calc
    ∫ ω, exp (θ * X ω * Y ω) ∂μ
        = ∫ p : ℝ × ℝ, g p ∂(μ.map φ) := by
          rw [integral_map hφ hg]
    _ = ∫ p : ℝ × ℝ, g p ∂((μ.map Y).prod (μ.map X)) := by rw [hmap_eq]
    _ ≤ exp (exp 1 ^ 2 * C0 ^ 2 * θ ^ 2) := hprod_bound

end NLAlib
