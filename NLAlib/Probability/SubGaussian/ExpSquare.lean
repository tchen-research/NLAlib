import NLAlib.Probability.SubGaussian.EvenMoments

/-!
# Square-exponential moments of sub-Gaussian variables

For `ProbabilityTheory.HasSubgaussianMGF X c μ` and a real proxy `C₀ ≥ c`, `C₀ > 0`:

* `integral_exp_mul_sq_eq_tsum_integrals`: `𝔼 e^{θ X²} = ∑ₘ 𝔼 θᵐ X^{2m} / m!` below the radius;
* `integral_exp_mul_sq_le_of_hasSubgaussianMGF`: `𝔼 e^{θ X²} ≤ e (1 - θ C₀ e)⁻¹` for
  `θ C₀ e < 1`, and the sharper forms isolating the first Taylor terms;
* `integral_exp_mul_sq_le_exp_linear_of_hasSubgaussianMGF_of_le`: `𝔼 e^{θ X²} ≤ e^{2e θ C₀ e}`
  for `θ C₀ e ≤ 1/2`;
* `integrable_exp_mul_sq_of_hasSubgaussianMGF{,_of_le}`: integrability of `e^{θ X²}`.

Vershynin 2018, Prop 2.5.2 (iii). Ported from HighDimProb commit
c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae (Hanson–Wright proof, Apache-2.0, authors Yuanhe Zhang,
Jason D. Lee, Fanghui Liu); atlas `hanson-wright` (helpers), `subgaussian-def`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Taylor integrals `𝔼 θᵐ X^{2m} / m!` of `𝔼 e^{θ X²}` are summable for
`0 ≤ θ` and `θ (c + 1) e < 1`. Atlas `hanson-wright` (helper). -/
theorem summable_integral_exp_sq_series_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hθ_small : θ * ((c : ℝ) + 1) * exp 1 < 1) :
    Summable fun m : ℕ =>
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ := by
  set r : ℝ := θ * ((c : ℝ) + 1) * exp 1 with hr_def
  have hr_nonneg : 0 ≤ r := by
    rw [hr_def]
    positivity
  have hgeom : Summable fun m : ℕ => exp 1 * r ^ m :=
    (summable_geometric_of_lt_one hr_nonneg (by simpa only [hr_def] using hθ_small)).mul_left
      (exp 1)
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro m
    exact integral_nonneg_of_ae (ae_of_all _ fun ω => by
      exact div_nonneg
        (mul_nonneg (pow_nonneg hθ m) (Even.pow_nonneg (even_two.mul_right m) (X ω)))
        (Nat.cast_nonneg (Nat.factorial m)))
  · intro m
    simpa only [hr_def] using integral_exp_sq_series_term_le_of_hasSubgaussianMGF h hθ m

/-- The Taylor integrals `𝔼 θᵐ X^{2m} / m!` of `𝔼 e^{θ X²}` are summable for
`0 ≤ θ` and `θ C₀ e < 1`, where `C₀ ≥ c` is a positive proxy. Atlas `hanson-wright` (helper). -/
theorem summable_integral_exp_sq_series_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_small : θ * C0 * exp 1 < 1) :
    Summable fun m : ℕ =>
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ := by
  set r : ℝ := θ * C0 * exp 1 with hr_def
  have hr_nonneg : 0 ≤ r := by
    rw [hr_def]
    positivity
  have hgeom : Summable fun m : ℕ => exp 1 * r ^ m :=
    (summable_geometric_of_lt_one hr_nonneg (by simpa only [hr_def] using hθ_small)).mul_left
      (exp 1)
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro m
    exact integral_nonneg_of_ae (ae_of_all _ fun ω => by
      exact div_nonneg
        (mul_nonneg (pow_nonneg hθ m) (Even.pow_nonneg (even_two.mul_right m) (X ω)))
        (Nat.cast_nonneg (Nat.factorial m)))
  · intro m
    simpa only [hr_def] using
      integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le m

/-- Integral form of the Taylor expansion: `𝔼 e^{θ X²} = ∑ₘ 𝔼 θᵐ X^{2m} / m!` whenever the
right side is summable. Atlas `hanson-wright` (helper). -/
theorem integral_exp_mul_sq_eq_tsum_integrals {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsum : Summable fun m : ℕ =>
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ) :
    ∫ ω, exp (θ * X ω ^ 2) ∂μ =
      ∑' m : ℕ, ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ := by
  let F : ℕ → Ω → ℝ :=
    fun m ω => θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ)
  have hF_nonneg : ∀ m : ℕ, 0 ≤ᵐ[μ] F m := by
    intro m
    exact ae_of_all _ fun ω => by
      dsimp [F]
      exact div_nonneg
        (mul_nonneg (pow_nonneg hθ m) (Even.pow_nonneg (even_two.mul_right m) (X ω)))
        (Nat.cast_nonneg (Nat.factorial m))
  have hF_int : ∀ m : ℕ, Integrable (F m) μ := by
    intro m
    have hpow : Integrable (fun ω => X ω ^ (2 * m)) μ := by
      exact integrable_pow_of_integrable_exp_mul
        (X := X) (t := 1) one_ne_zero
        (h.integrable_exp_mul 1)
        (h.integrable_exp_mul (-1))
        (2 * m)
    dsimp [F]
    exact (hpow.const_mul (θ ^ m)).div_const _
  have hF_sum_norm : Summable fun m : ℕ => ∫ ω, ‖F m ω‖ ∂μ := by
    convert hsum using 1
    ext m
    apply integral_congr_ae
    filter_upwards [hF_nonneg m] with ω hω
    rw [Real.norm_of_nonneg hω]
  have htsum := integral_tsum_of_summable_integral_norm hF_int hF_sum_norm
  change ∫ ω, exp (θ * X ω ^ 2) ∂μ = ∑' m : ℕ, ∫ ω, F m ω ∂μ
  rw [htsum]
  apply integral_congr_ae
  filter_upwards with ω
  dsimp [F]
  rw [exp_mul_sq_eq_tsum θ (X ω)]

/-- Exponential-square bound: if `X` is sub-Gaussian with proxy `c ≤ C₀` and
`θ C₀ e < 1`, then `𝔼 e^{θ X²} ≤ e (1 - θ C₀ e)⁻¹`. Vershynin 2018, Prop 2.5.2 (iii);
atlas `hanson-wright` (helper). -/
theorem integral_exp_mul_sq_le_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_small : θ * C0 * exp 1 < 1) :
    ∫ ω, exp (θ * X ω ^ 2) ∂μ ≤ exp 1 * (1 - θ * C0 * exp 1)⁻¹ := by
  set r : ℝ := θ * C0 * exp 1 with hr_def
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  have hr_lt : r < 1 := by simpa only [hr_def] using hθ_small
  have hsum :=
    summable_integral_exp_sq_series_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le hθ_small
  have hgeom : Summable fun m : ℕ => exp 1 * r ^ m :=
    (summable_geometric_of_lt_one hr_nonneg hr_lt).mul_left (exp 1)
  rw [integral_exp_mul_sq_eq_tsum_integrals h hθ hsum]
  calc
    (∑' m : ℕ, ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ)
        ≤ ∑' m : ℕ, exp 1 * r ^ m := by
          refine Summable.tsum_le_tsum ?_ hsum hgeom
          intro m
          simpa only [hr_def] using
            integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le m
    _ = exp 1 * (1 - r)⁻¹ := by
          rw [tsum_mul_left]
          rw [tsum_geometric_of_lt_one hr_nonneg hr_lt]
    _ = exp 1 * (1 - θ * C0 * exp 1)⁻¹ := by rw [hr_def]

/-- Sharper exponential-square bound isolating the zeroth Taylor term:
`𝔼 e^{θ X²} ≤ 1 + e · r (1 - r)⁻¹` with `r = θ C₀ e < 1`. Atlas `hanson-wright` (helper). -/
theorem integral_exp_mul_sq_le_one_add_tail_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_small : θ * C0 * exp 1 < 1) :
    ∫ ω, exp (θ * X ω ^ 2) ∂μ ≤
      1 + exp 1 * ((θ * C0 * exp 1) * (1 - θ * C0 * exp 1)⁻¹) := by
  set r : ℝ := θ * C0 * exp 1 with hr_def
  let term : ℕ → ℝ :=
    fun m => ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  have hr_lt : r < 1 := by simpa only [hr_def] using hθ_small
  have hsum : Summable term := by
    simpa only [term] using
      summable_integral_exp_sq_series_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le hθ_small
  have hterm0 : term 0 = 1 := by
    change (∫ ω : Ω, θ ^ (0 : ℕ) * X ω ^ (2 * 0) /
      (Nat.factorial 0 : ℝ) ∂μ) = 1
    have hfun :
        (fun ω : Ω => θ ^ 0 * X ω ^ (2 * 0) / (Nat.factorial 0 : ℝ)) =
          (fun _ : Ω => (1 : ℝ)) := by
      funext ω
      norm_num
    rw [hfun]
    rw [integral_const, probReal_univ]
    norm_num
  have htail_sum : Summable fun n : ℕ => term (n + 1) := by
    exact (summable_nat_add_iff (f := term) 1).mpr hsum
  have hgeom_tail : Summable fun n : ℕ => exp 1 * r ^ (n + 1) := by
    have hgeom_base : Summable fun n : ℕ => r ^ n :=
      summable_geometric_of_lt_one hr_nonneg hr_lt
    have hgeom_shift : Summable fun n : ℕ => r ^ (n + 1) :=
      (summable_nat_add_iff (f := fun n : ℕ => r ^ n) 1).mpr hgeom_base
    exact hgeom_shift.mul_left (exp 1)
  rw [integral_exp_mul_sq_eq_tsum_integrals h hθ (by simpa only [term] using hsum)]
  change (∑' m : ℕ, term m) ≤ 1 + exp 1 * (r * (1 - r)⁻¹)
  rw [hsum.tsum_eq_zero_add, hterm0]
  gcongr
  calc
    (∑' n : ℕ, term (n + 1)) ≤ ∑' n : ℕ, exp 1 * r ^ (n + 1) := by
      refine Summable.tsum_le_tsum ?_ htail_sum hgeom_tail
      intro n
      simpa only [term, hr_def] using
        integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le (n + 1)
    _ = exp 1 * (r * (1 - r)⁻¹) := by
      rw [tsum_mul_left]
      rw [show (∑' n : ℕ, r ^ (n + 1)) = r * (1 - r)⁻¹ by
        have hgeom_base : Summable fun n : ℕ => r ^ n :=
          summable_geometric_of_lt_one hr_nonneg hr_lt
        have hsplit := hgeom_base.sum_add_tsum_nat_add 1
        rw [Finset.sum_range_one, tsum_geometric_of_lt_one hr_nonneg hr_lt] at hsplit
        have hshift : (∑' n : ℕ, r ^ (n + 1)) = (1 - r)⁻¹ - 1 := by
          linarith
        rw [hshift]
        have hden : 1 - r ≠ 0 := by linarith
        field_simp [hden]
        ring]

/-- Exponential-square bound isolating the zeroth and first Taylor terms:
`𝔼 e^{θ X²} ≤ 1 + θ 𝔼 X² + e · r² (1 - r)⁻¹` with `r = θ C₀ e < 1`. Atlas `hanson-wright`
(helper). -/
theorem integral_exp_mul_sq_le_one_add_linear_add_tail_of_hasSubgaussianMGF_of_le
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_small : θ * C0 * exp 1 < 1) :
    ∫ ω, exp (θ * X ω ^ 2) ∂μ ≤
      1 + θ * ∫ ω, X ω ^ 2 ∂μ +
        exp 1 * (((θ * C0 * exp 1) ^ 2) * (1 - θ * C0 * exp 1)⁻¹) := by
  set r : ℝ := θ * C0 * exp 1 with hr_def
  let term : ℕ → ℝ :=
    fun m => ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  have hr_lt : r < 1 := by simpa only [hr_def] using hθ_small
  have hsum : Summable term := by
    simpa only [term] using
      summable_integral_exp_sq_series_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le hθ_small
  have hterm0 : term 0 = 1 := by
    change (∫ ω : Ω, θ ^ (0 : ℕ) * X ω ^ (2 * 0) /
      (Nat.factorial 0 : ℝ) ∂μ) = 1
    have hfun :
        (fun ω : Ω => θ ^ 0 * X ω ^ (2 * 0) / (Nat.factorial 0 : ℝ)) =
          (fun _ : Ω => (1 : ℝ)) := by
      funext ω
      norm_num
    rw [hfun]
    rw [integral_const, probReal_univ]
    norm_num
  have hterm1 : term 1 = θ * ∫ ω, X ω ^ 2 ∂μ := by
    change (∫ ω : Ω, θ ^ (1 : ℕ) * X ω ^ (2 * 1) /
      (Nat.factorial 1 : ℝ) ∂μ) = θ * ∫ ω, X ω ^ 2 ∂μ
    have hfun :
        (fun ω : Ω => θ ^ 1 * X ω ^ (2 * 1) / (Nat.factorial 1 : ℝ)) =
          (fun ω : Ω => θ * X ω ^ 2) := by
      funext ω
      norm_num
    rw [hfun, integral_const_mul]
  have htail_sum : Summable fun n : ℕ => term (n + 2) := by
    exact (summable_nat_add_iff (f := term) 2).mpr hsum
  have hgeom_tail : Summable fun n : ℕ => exp 1 * r ^ (n + 2) := by
    have hgeom_base : Summable fun n : ℕ => r ^ n :=
      summable_geometric_of_lt_one hr_nonneg hr_lt
    have hgeom_shift : Summable fun n : ℕ => r ^ (n + 2) :=
      (summable_nat_add_iff (f := fun n : ℕ => r ^ n) 2).mpr hgeom_base
    exact hgeom_shift.mul_left (exp 1)
  rw [integral_exp_mul_sq_eq_tsum_integrals h hθ (by simpa only [term] using hsum)]
  change (∑' m : ℕ, term m) ≤
    1 + θ * ∫ ω, X ω ^ 2 ∂μ + exp 1 * (r ^ 2 * (1 - r)⁻¹)
  have hsplit := hsum.sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ, Finset.sum_range_one, hterm0, hterm1] at hsplit
  rw [← hsplit]
  gcongr
  calc
    (∑' n : ℕ, term (n + 2)) ≤ ∑' n : ℕ, exp 1 * r ^ (n + 2) := by
      refine Summable.tsum_le_tsum ?_ htail_sum hgeom_tail
      intro n
      simpa only [term, hr_def] using
        integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le (n + 2)
    _ = exp 1 * (r ^ 2 * (1 - r)⁻¹) := by
      rw [tsum_mul_left]
      rw [show (∑' n : ℕ, r ^ (n + 2)) = r ^ 2 * (1 - r)⁻¹ by
        have hgeom_base : Summable fun n : ℕ => r ^ n :=
          summable_geometric_of_lt_one hr_nonneg hr_lt
        have hsplit2 := hgeom_base.sum_add_tsum_nat_add 2
        rw [Finset.sum_range_succ, Finset.sum_range_one,
          tsum_geometric_of_lt_one hr_nonneg hr_lt] at hsplit2
        have hshift : (∑' n : ℕ, r ^ (n + 2)) = (1 - r)⁻¹ - (1 + r) := by
          linarith
        rw [hshift]
        have hden : 1 - r ≠ 0 := by linarith
        field_simp [hden]
        ring]

/-- Linear-in-`θ` exponential-square bound at half the radius: `𝔼 e^{θ X²} ≤ e^{2e r}` with
`r = θ C₀ e ≤ 1/2`. Atlas `hanson-wright` (helper). -/
theorem integral_exp_mul_sq_le_exp_linear_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_half : θ * C0 * exp 1 ≤ 1 / 2) :
    ∫ ω, exp (θ * X ω ^ 2) ∂μ ≤ exp (2 * exp 1 * (θ * C0 * exp 1)) := by
  set r : ℝ := θ * C0 * exp 1 with hr_def
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  have hr_half : r ≤ 1 / 2 := by simpa only [hr_def] using hθ_half
  have hr_lt : r < 1 := by linarith
  have hbase :=
    integral_exp_mul_sq_le_one_add_tail_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le
      (by simpa only [hr_def] using hr_lt)
  have hden_pos : 0 < 1 - r := by linarith
  have hinv_le : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden_pos two_pos]
    linarith
  have htail :
      exp 1 * (r * (1 - r)⁻¹) ≤ 2 * exp 1 * r := by
    have hmul : r * (1 - r)⁻¹ ≤ r * 2 :=
      mul_le_mul_of_nonneg_left hinv_le hr_nonneg
    calc
      exp 1 * (r * (1 - r)⁻¹) ≤ exp 1 * (r * 2) :=
        mul_le_mul_of_nonneg_left hmul (exp_pos 1).le
      _ = 2 * exp 1 * r := by ring
  calc
    ∫ ω, exp (θ * X ω ^ 2) ∂μ
        ≤ 1 + exp 1 * (r * (1 - r)⁻¹) := by
          simpa only [hr_def] using hbase
    _ ≤ 1 + 2 * exp 1 * r := by linarith
    _ ≤ exp (2 * exp 1 * r) := by
          simpa [add_comm] using Real.add_one_le_exp (2 * exp 1 * r)
    _ = exp (2 * exp 1 * (θ * C0 * exp 1)) := by rw [hr_def]

/-! ### Integrability -/

/-- `e^{θ X²}` is integrable as soon as its Taylor integrals `𝔼 θᵐ X^{2m} / m!` are summable
(`θ ≥ 0`). Atlas `hanson-wright` (helper). -/
theorem integrable_exp_mul_sq_of_summable_integrals {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsum : Summable fun m : ℕ =>
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ) :
    Integrable (fun ω => exp (θ * X ω ^ 2)) μ := by
  let F : ℕ → Ω → ℝ :=
    fun m ω => θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ)
  have hF_nonneg : ∀ m : ℕ, 0 ≤ᵐ[μ] F m := by
    intro m
    exact ae_of_all _ fun ω => by
      dsimp [F]
      exact div_nonneg
        (mul_nonneg (pow_nonneg hθ m) (Even.pow_nonneg (even_two.mul_right m) (X ω)))
        (Nat.cast_nonneg (Nat.factorial m))
  have hF_int : ∀ m : ℕ, Integrable (F m) μ := by
    intro m
    have hpow : Integrable (fun ω => X ω ^ (2 * m)) μ := by
      exact integrable_pow_of_integrable_exp_mul
        (X := X) (t := 1) one_ne_zero
        (h.integrable_exp_mul 1)
        (h.integrable_exp_mul (-1))
        (2 * m)
    dsimp [F]
    exact (hpow.const_mul (θ ^ m)).div_const _
  have hF_integral_nonneg : ∀ m : ℕ, 0 ≤ ∫ ω, F m ω ∂μ := by
    intro m
    exact integral_nonneg_of_ae (hF_nonneg m)
  have hF_lintegral_eq :
      (∑' m : ℕ, ∫⁻ ω, ENNReal.ofReal (F m ω) ∂μ) =
        ENNReal.ofReal (∑' m : ℕ, ∫ ω, F m ω ∂μ) := by
    calc (∑' m : ℕ, ∫⁻ ω, ENNReal.ofReal (F m ω) ∂μ)
        = ∑' m : ℕ, ENNReal.ofReal (∫ ω, F m ω ∂μ) := by
          congr with m
          exact (ofReal_integral_eq_lintegral_ofReal (hF_int m) (hF_nonneg m)).symm
      _ = ENNReal.ofReal (∑' m : ℕ, ∫ ω, F m ω ∂μ) := by
          exact (ENNReal.ofReal_tsum_of_nonneg hF_integral_nonneg hsum).symm
  have h_exp_lintegral_eq :
      ∫⁻ ω, ENNReal.ofReal (exp (θ * X ω ^ 2)) ∂μ =
        ∑' m : ℕ, ∫⁻ ω, ENNReal.ofReal (F m ω) ∂μ := by
    calc ∫⁻ ω, ENNReal.ofReal (exp (θ * X ω ^ 2)) ∂μ
        = ∫⁻ ω, ∑' m : ℕ, ENNReal.ofReal (F m ω) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards with ω
          have hsummable :
              Summable fun m : ℕ => F m ω := by
            convert Real.summable_pow_div_factorial (θ * X ω ^ 2) using 1
            ext m
            dsimp [F]
            rw [mul_pow, ← pow_mul]
          rw [exp_mul_sq_eq_tsum θ (X ω)]
          exact ENNReal.ofReal_tsum_of_nonneg
            (fun m => by
              show 0 ≤ θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ)
              exact div_nonneg
                (mul_nonneg (pow_nonneg hθ m)
                  (Even.pow_nonneg (even_two.mul_right m) (X ω)))
                (Nat.cast_nonneg (Nat.factorial m))) hsummable
      _ = ∑' m : ℕ, ∫⁻ ω, ENNReal.ofReal (F m ω) ∂μ := by
          rw [lintegral_tsum]
          intro m
          exact (hF_int m).aemeasurable.ennreal_ofReal
  have h_exp_lintegral_ne_top :
      ∫⁻ ω, ENNReal.ofReal (exp (θ * X ω ^ 2)) ∂μ ≠ ⊤ := by
    rw [h_exp_lintegral_eq, hF_lintegral_eq]
    exact ENNReal.ofReal_ne_top
  exact (lintegral_ofReal_ne_top_iff_integrable
    ((h.aemeasurable.pow_const 2).const_mul θ).exp.aestronglyMeasurable
    (ae_of_all _ fun ω => (exp_pos _).le)).mp h_exp_lintegral_ne_top

/-- `e^{θ X²}` is integrable for a sub-Gaussian `X` when `0 ≤ θ` and `θ (c + 1) e < 1`.
Atlas `hanson-wright` (helper). -/
theorem integrable_exp_mul_sq_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hθ_small : θ * ((c : ℝ) + 1) * exp 1 < 1) :
    Integrable (fun ω => exp (θ * X ω ^ 2)) μ :=
  integrable_exp_mul_sq_of_summable_integrals h hθ
    (summable_integral_exp_sq_series_of_hasSubgaussianMGF h hθ hθ_small)

/-- `e^{θ X²}` is integrable for a sub-Gaussian `X` when `0 ≤ θ` and `θ C₀ e < 1` for a positive
proxy `C₀ ≥ c`. Atlas `hanson-wright` (helper). -/
theorem integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_small : θ * C0 * exp 1 < 1) :
    Integrable (fun ω => exp (θ * X ω ^ 2)) μ :=
  integrable_exp_mul_sq_of_summable_integrals h hθ
    (summable_integral_exp_sq_series_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le hθ_small)

end NLAlib
