import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Convex.Integral
import NLAlib.ForMathlib.Analysis.ExpBounds

/-!
# Sub-Gaussian variables: mean, even moments and square-exponential Taylor terms

Scalar consequences of Mathlib's `ProbabilityTheory.HasSubgaussianMGF X c μ`:

* `hasSubgaussianMGF_mono` (monotonicity in the proxy) and
  `hasSubgaussianMGF_finset_sum_mul_of_iIndepFun` (independent linear combinations);
* `integral_eq_zero_of_hasSubgaussianMGF`: a sub-Gaussian variable is centred;
* `hasSubgaussianMGF_of_abs_le_of_integral_eq_zero`: bounded centred variables (Hoeffding's lemma);
* `integral_pow_two_mul_le_of_hasSubgaussianMGF`: `𝔼 X^{2m} ≤ (2m)!/s^{2m} · e^{c s²/2}`;
* `integral_exp_sq_series_term_le_of_hasSubgaussianMGF{,_of_le}`: geometric bounds for the
  Taylor terms `𝔼 θᵐ X^{2m} / m!` of `𝔼 e^{θ X²}`, and the second and fourth moments.

The square-exponential bounds built from these are in
`NLAlib.Probability.SubGaussian.ExpSquare`. Vershynin 2018, Prop 2.5.2. Ported from HighDimProb
(Hanson–Wright proof, Apache-2.0, authors
Yuanhe Zhang, Jason D. Lee, Fanghui Liu); atlas `hanson-wright` (helpers), `subgaussian-def`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Basic API -/

/-- Monotonicity in the variance proxy: `HasSubgaussianMGF X c μ` and `c ≤ d` give
`HasSubgaussianMGF X d μ`. Atlas `hanson-wright` (helper). -/
theorem hasSubgaussianMGF_mono {μ : Measure Ω} {X : Ω → ℝ} {c d : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hcd : (c : ℝ) ≤ d) :
    HasSubgaussianMGF X d μ where
  integrable_exp_mul t := h.integrable_exp_mul t
  mgf_le t := by
    have hmul : (c : ℝ) * t ^ 2 ≤ (d : ℝ) * t ^ 2 :=
      mul_le_mul_of_nonneg_right hcd (sq_nonneg t)
    calc
      mgf X μ t ≤ exp ((c : ℝ) * t ^ 2 / 2) := h.mgf_le t
      _ ≤ exp ((d : ℝ) * t ^ 2 / 2) := by
          exact exp_le_exp.mpr (by linarith)

/-- A finite linear combination `∑_{i ∈ s} aᵢ Xᵢ` of independent sub-Gaussian variables is
sub-Gaussian with proxy `∑_{i ∈ s} aᵢ² cᵢ`. Vershynin 2018, Prop 2.6.1; atlas `hanson-wright`
(helper). -/
theorem hasSubgaussianMGF_finset_sum_mul_of_iIndepFun {ι : Type*} {μ : Measure Ω}
    {X : ι → Ω → ℝ} (hind : iIndepFun X μ) {c : ι → ℝ≥0}
    {s : Finset ι} (hmgf : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ)
    (a : ι → ℝ) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ s, a i * X i ω)
      (∑ i ∈ s, Real.toNNReal (a i ^ 2) * c i) μ := by
  have hind_mul :
      iIndepFun (fun i => fun ω => a i * X i ω) μ := by
    simpa [Function.comp_def] using
      hind.comp (fun i x => a i * x) (fun i => by fun_prop)
  have hmgf_mul :
      ∀ i ∈ s, HasSubgaussianMGF (fun ω => a i * X i ω)
      (Real.toNNReal (a i ^ 2) * c i) μ := by
    intro i hi
    convert (hmgf i hi).const_mul (a i) using 1
    rw [Real.toNNReal_of_nonneg (sq_nonneg (a i))]
    rfl
  exact HasSubgaussianMGF.sum_of_iIndepFun hind_mul hmgf_mul

/-- Jensen's inequality for the exponential, in logarithmic form: `𝔼 X ≤ t⁻¹ log 𝔼 e^{tX}` for
`t > 0` when `X` and `e^{tX}` are integrable. Atlas `hanson-wright` (helper). -/
theorem integral_le_one_div_mul_log_integral_exp_mul {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_int : Integrable X μ) {t : ℝ} (ht : 0 < t)
    (hexpX_int : Integrable (fun ω => exp (t * X ω)) μ) :
    ∫ ω, X ω ∂μ ≤ (1 / t) * log (∫ ω, exp (t * X ω) ∂μ) := by
  have h := (convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (by simp) (hX_int.const_mul t) hexpX_int)
  have h1 : ∫ ω, t * X ω ∂μ = t * ∫ ω, X ω ∂μ := integral_const_mul t X
  have h2 : t * ∫ ω, X ω ∂μ ≤ log (∫ ω, exp (t * X ω) ∂μ) := by
    have hexp_bound : exp (t * ∫ ω, X ω ∂μ) ≤ ∫ ω, exp (t * X ω) ∂μ := h1 ▸ h
    calc
      t * ∫ ω, X ω ∂μ = log (exp (t * ∫ ω, X ω ∂μ)) := (log_exp _).symm
      _ ≤ log (∫ ω, exp (t * X ω) ∂μ) :=
        log_le_log (exp_pos _) hexp_bound
  calc
    ∫ ω, X ω ∂μ = (∫ ω, X ω ∂μ) * t / t := by
      calc
        ∫ ω, X ω ∂μ = (∫ ω, X ω ∂μ) * 1 := by ring
        _ = (∫ ω, X ω ∂μ) * (t / t) := by rw [div_self ht.ne']
        _ = (∫ ω, X ω ∂μ) * t / t := by ring
    _ ≤ log (∫ ω, exp (t * X ω) ∂μ) / t := by
      exact div_le_div_of_nonneg_right (by linarith) ht.le
    _ = (1 / t) * log (∫ ω, exp (t * X ω) ∂μ) := by ring

/-- A variable with a sub-Gaussian MGF bound has nonpositive mean, `𝔼 X ≤ 0` (apply
`integral_le_one_div_mul_log_integral_exp_mul` and let `t → 0`). Atlas `hanson-wright` (helper). -/
theorem integral_nonpos_of_hasSubgaussianMGF {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ∂μ ≤ 0 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set t : ℝ := ε / ((c : ℝ) + 1) with ht_def
  have hden_pos : 0 < (c : ℝ) + 1 := by positivity
  have ht_pos : 0 < t := by
    rw [ht_def]
    positivity
  have hmean := integral_le_one_div_mul_log_integral_exp_mul h.integrable ht_pos
    (h.integrable_exp_mul t)
  have hmgf_pos : 0 < mgf X μ t := mgf_pos (h.integrable_exp_mul t)
  have hlog_le : log (mgf X μ t) ≤ (c : ℝ) * t ^ 2 / 2 := by
    calc
      log (mgf X μ t) ≤ log (exp ((c : ℝ) * t ^ 2 / 2)) :=
        log_le_log hmgf_pos (h.mgf_le t)
      _ = (c : ℝ) * t ^ 2 / 2 := log_exp _
  have hmean_le : ∫ ω, X ω ∂μ ≤ (1 / t) * ((c : ℝ) * t ^ 2 / 2) :=
    hmean.trans (mul_le_mul_of_nonneg_left hlog_le (by positivity))
  calc
    ∫ ω, X ω ∂μ ≤ (1 / t) * ((c : ℝ) * t ^ 2 / 2) := hmean_le
    _ = (c : ℝ) * t / 2 := by field_simp [ht_pos.ne']
    _ ≤ ε := by
      rw [ht_def]
      have hratio : (c : ℝ) / ((c : ℝ) + 1) ≤ 1 :=
        (div_le_one hden_pos).mpr (by linarith)
      calc
        (c : ℝ) * (ε / ((c : ℝ) + 1)) / 2 =
            (ε / 2) * ((c : ℝ) / ((c : ℝ) + 1)) := by ring
        _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
        _ ≤ ε := by linarith
    _ = 0 + ε := by ring

/-- A random variable with a sub-Gaussian MGF bound (for every real `t`) is centred:
`𝔼 X = 0`. Vershynin 2018, Prop 2.5.2 (v) ⇒ mean zero; atlas `hanson-wright` (helper). -/
theorem integral_eq_zero_of_hasSubgaussianMGF {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ∂μ = 0 := by
  have hle : ∫ ω, X ω ∂μ ≤ 0 := integral_nonpos_of_hasSubgaussianMGF h
  have hle_neg : ∫ ω, -X ω ∂μ ≤ 0 := integral_nonpos_of_hasSubgaussianMGF h.neg
  have hge : 0 ≤ ∫ ω, X ω ∂μ := by
    rw [integral_neg] at hle_neg
    linarith
  exact le_antisymm hle hge

/-- Bounded centred variables are sub-Gaussian: if `|Y| ≤ R` a.e. and `𝔼 Y = 0`, then
`HasSubgaussianMGF Y R²`. Hoeffding's lemma on `[-R, R]` (Mathlib
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`). Atlas `hanson-wright` (helper). -/
theorem hasSubgaussianMGF_of_abs_le_of_integral_eq_zero {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} {R : ℝ}
    (hY_meas : AEMeasurable Y μ) (hR : 0 ≤ R)
    (hY_bound : ∀ᵐ ω ∂μ, |Y ω| ≤ R) (hY_center : ∫ ω, Y ω ∂μ = 0) :
    HasSubgaussianMGF Y ⟨R ^ 2, sq_nonneg R⟩ μ := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hY_meas
    (hY_bound.mono fun ω hω => abs_le.mp hω) hY_center
  have hc : ((‖R - -R‖₊ / 2) ^ 2 : ℝ≥0) = ⟨R ^ 2, sq_nonneg R⟩ := by
    apply NNReal.eq
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, sub_neg_eq_add,
      NNReal.coe_ofNat]
    rw [← two_mul, abs_mul, abs_of_nonneg hR]
    norm_num
    rfl
  rw [← hc]
  exact h

/-! ### Even moments -/

/-- Two-sided consequence of a sub-Gaussian MGF bound: `𝔼 cosh (t X) ≤ e^{c t²/2}`.
Atlas `hanson-wright` (helper). -/
theorem integral_cosh_mul_le_of_hasSubgaussianMGF {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) (t : ℝ) :
    ∫ ω, cosh (t * X ω) ∂μ ≤ exp ((c : ℝ) * t ^ 2 / 2) := by
  have hint_pos : Integrable (fun ω => exp (t * X ω)) μ :=
    h.integrable_exp_mul t
  have hint_neg : Integrable (fun ω => exp (-(t * X ω))) μ := by
    convert h.integrable_exp_mul (-t) using 1
    ext ω
    ring_nf
  have h_eq :
      ∫ ω, cosh (t * X ω) ∂μ =
        (mgf X μ t + mgf X μ (-t)) / 2 := by
    calc ∫ ω, cosh (t * X ω) ∂μ
        = ∫ ω, (exp (t * X ω) + exp (-(t * X ω))) / 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [Real.cosh_eq]
      _ = (∫ ω, exp (t * X ω) + exp (-(t * X ω)) ∂μ) / 2 := by
          rw [integral_div]
      _ = (mgf X μ t + mgf X μ (-t)) / 2 := by
          rw [integral_add hint_pos hint_neg]
          change (∫ ω, exp (t * X ω) ∂μ + ∫ ω, exp (-(t * X ω)) ∂μ) / 2 =
            (∫ ω, exp (t * X ω) ∂μ + ∫ ω, exp (-t * X ω) ∂μ) / 2
          simp only [neg_mul]
  rw [h_eq]
  have hpos_le : mgf X μ t ≤ exp ((c : ℝ) * t ^ 2 / 2) :=
    h.mgf_le t
  have hneg_le : mgf X μ (-t) ≤ exp ((c : ℝ) * t ^ 2 / 2) := by
    simpa [sq] using h.mgf_le (-t)
  nlinarith [hpos_le, hneg_le]

/-- Sub-Gaussian MGF control bounds every integrated even Taylor term:
`𝔼 (tX)^{2m} / (2m)! ≤ e^{c t²/2}`. Atlas `hanson-wright` (helper). -/
theorem integral_even_taylor_term_le_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (t : ℝ) (m : ℕ) :
    ∫ ω, (t * X ω) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ∂μ
      ≤ exp ((c : ℝ) * t ^ 2 / 2) := by
  have hint_pos : Integrable (fun ω => exp (t * X ω)) μ :=
    h.integrable_exp_mul t
  have hint_neg : Integrable (fun ω => exp (-(t * X ω))) μ := by
    convert h.integrable_exp_mul (-t) using 1
    ext ω
    ring_nf
  have hterm_int :
      Integrable (fun ω => (t * X ω) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) μ := by
    have hpow :
        Integrable (fun ω => (t * X ω) ^ (2 * m)) μ := by
      exact integrable_pow_of_integrable_exp_mul
        (X := fun ω => t * X ω) (t := 1) one_ne_zero
        (by
          convert hint_pos using 1
          ext ω
          ring_nf)
        (by
          convert hint_neg using 1
          ext ω
          ring_nf)
        (2 * m)
    exact hpow.div_const _
  have hcosh_int : Integrable (fun ω => cosh (t * X ω)) μ := by
    have hsum : Integrable (fun ω => exp (t * X ω) + exp (-(t * X ω))) μ :=
      hint_pos.add hint_neg
    convert hsum.div_const 2 using 1
    ext ω
    rw [Real.cosh_eq]
  calc ∫ ω, (t * X ω) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ∂μ
      ≤ ∫ ω, cosh (t * X ω) ∂μ := by
        exact integral_mono_ae hterm_int hcosh_int
          (ae_of_all _ fun ω => cosh_taylor_term_le (t * X ω) m)
    _ ≤ exp ((c : ℝ) * t ^ 2 / 2) :=
        integral_cosh_mul_le_of_hasSubgaussianMGF h t

/-- Even moments of a sub-Gaussian variable: for every scale `s > 0`,
`𝔼 X^{2m} ≤ (2m)!/s^{2m} · e^{c s²/2}`. Vershynin 2018, Prop 2.5.2 (moment step);
atlas `hanson-wright` (helper). -/
theorem integral_pow_two_mul_le_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {s : ℝ} (hs : 0 < s) (m : ℕ) :
    ∫ ω, X ω ^ (2 * m) ∂μ
      ≤ (Nat.factorial (2 * m) : ℝ) / s ^ (2 * m) *
        exp ((c : ℝ) * s ^ 2 / 2) := by
  have hle := integral_even_taylor_term_le_of_hasSubgaussianMGF h s m
  have hscale :
      ∫ ω, (s * X ω) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ∂μ =
        (s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) *
          ∫ ω, X ω ^ (2 * m) ∂μ := by
    calc ∫ ω, (s * X ω) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ∂μ
        = ∫ ω, (s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) *
            X ω ^ (2 * m) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [mul_pow]
          ring
      _ = (s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) *
          ∫ ω, X ω ^ (2 * m) ∂μ := by
          rw [integral_const_mul]
  rw [hscale] at hle
  have hcoef_pos :
      0 < s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) := by
    positivity
  have hbound :
      ∫ ω, X ω ^ (2 * m) ∂μ
        ≤ exp ((c : ℝ) * s ^ 2 / 2) /
          (s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) := by
    rw [le_div_iff₀ hcoef_pos]
    nlinarith [hle]
  calc ∫ ω, X ω ^ (2 * m) ∂μ
      ≤ exp ((c : ℝ) * s ^ 2 / 2) /
          (s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) := hbound
    _ = (Nat.factorial (2 * m) : ℝ) / s ^ (2 * m) *
        exp ((c : ℝ) * s ^ 2 / 2) := by
        field_simp [ne_of_gt hs, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * m))]

/-- Geometric bound for each integrated Taylor term of `e^{θ X²}`:
`𝔼 θᵐ X^{2m} / m! ≤ e · (θ (c + 1) e)ᵐ`. Atlas `hanson-wright` (helper). -/
theorem integral_exp_sq_series_term_le_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 0 ≤ θ) (m : ℕ) :
    ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
      ≤ exp 1 * (θ * ((c : ℝ) + 1) * exp 1) ^ m := by
  let q : ℝ := ((2 * m + 1 : ℕ) : ℝ) / ((c : ℝ) + 1)
  let s : ℝ := sqrt q
  have hc1_pos : 0 < (c : ℝ) + 1 := by positivity
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hq_nonneg : 0 ≤ q := hq_pos.le
  have hs_pos : 0 < s := by
    dsimp [s]
    exact sqrt_pos.mpr hq_pos
  have hs_pow : s ^ (2 * m) = q ^ m := by
    dsimp [s]
    rw [pow_mul, sq_sqrt hq_nonneg]
  have hs_sq : s ^ 2 = q := by
    dsimp [s]
    rw [sq_sqrt hq_nonneg]
  have hmoment := integral_pow_two_mul_le_of_hasSubgaussianMGF h hs_pos m
  have hterm_eq :
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ =
        (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ := by
    calc ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
        = ∫ ω, (θ ^ m / (Nat.factorial m : ℝ)) * X ω ^ (2 * m) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
      _ = (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ := by
          rw [integral_const_mul]
  rw [hterm_eq]
  have hcoef_nonneg : 0 ≤ θ ^ m / (Nat.factorial m : ℝ) := by
    positivity
  calc (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ
      ≤ (θ ^ m / (Nat.factorial m : ℝ)) *
          ((Nat.factorial (2 * m) : ℝ) / s ^ (2 * m) *
            exp ((c : ℝ) * s ^ 2 / 2)) := by
        exact mul_le_mul_of_nonneg_left hmoment hcoef_nonneg
    _ = θ ^ m *
          (((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m) *
            exp ((c : ℝ) * q / 2) := by
        rw [hs_pow, hs_sq]
        field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
    _ ≤ θ ^ m * (((c : ℝ) + 1) ^ m) * exp (m + 1 : ℝ) := by
        have hfac := factorial_two_mul_div_factorial_le_succ_pow m
        have hratio :
            ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m
              ≤ ((c : ℝ) + 1) ^ m := by
          have hnum_pos : 0 < (((2 * m + 1 : ℕ) : ℝ) ^ m) := by positivity
          have hc1pow_nonneg : 0 ≤ ((c : ℝ) + 1) ^ m := by positivity
          calc
            ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m
                = ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) *
                  (((c : ℝ) + 1) ^ m / (((2 * m + 1 : ℕ) : ℝ) ^ m)) := by
                    dsimp [q]
                    rw [div_pow]
                    field_simp [hc1_pos.ne']
            _ ≤ (((2 * m + 1 : ℕ) : ℝ) ^ m) *
                  (((c : ℝ) + 1) ^ m / (((2 * m + 1 : ℕ) : ℝ) ^ m)) := by
                    exact mul_le_mul_of_nonneg_right hfac
                      (div_nonneg hc1pow_nonneg hnum_pos.le)
            _ = ((c : ℝ) + 1) ^ m := by
                    field_simp [ne_of_gt hnum_pos]
        have hexp_le : exp ((c : ℝ) * q / 2) ≤ exp (m + 1 : ℝ) := by
          apply exp_le_exp.mpr
          have hc_le : (c : ℝ) / ((c : ℝ) + 1) ≤ 1 := by
            rw [div_le_one hc1_pos]
            linarith
          have hnon : 0 ≤ ((2 * m + 1 : ℕ) : ℝ) / 2 := by positivity
          calc
            (c : ℝ) * q / 2 =
                ((c : ℝ) / ((c : ℝ) + 1)) * (((2 * m + 1 : ℕ) : ℝ) / 2) := by
                  dsimp [q]
                  field_simp [hc1_pos.ne']
            _ ≤ 1 * (((2 * m + 1 : ℕ) : ℝ) / 2) :=
                mul_le_mul_of_nonneg_right hc_le hnon
            _ ≤ (m + 1 : ℝ) := by
                norm_num
                nlinarith
        calc
          θ ^ m * (((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m) *
              exp ((c : ℝ) * q / 2)
              ≤ θ ^ m * ((c : ℝ) + 1) ^ m * exp ((c : ℝ) * q / 2) := by
                gcongr
          _ ≤ θ ^ m * ((c : ℝ) + 1) ^ m * exp (m + 1 : ℝ) := by
                gcongr
    _ = exp 1 * (θ * ((c : ℝ) + 1) * exp 1) ^ m := by
        rw [show (m + 1 : ℝ) = (m : ℝ) + 1 by norm_num, exp_add]
        rw [show exp (m : ℝ) = exp 1 ^ m by
          rw [show (m : ℝ) = (m : ℝ) * 1 by ring, Real.exp_nat_mul]]
        rw [mul_pow, mul_pow]
        ring

/-- Geometric Taylor-term bound with any real proxy `C₀ ≥ c`, `C₀ > 0`:
`𝔼 θᵐ X^{2m} / m! ≤ e · (θ C₀ e)ᵐ`. Atlas `hanson-wright` (helper). -/
theorem integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0) (m : ℕ) :
    ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
      ≤ exp 1 * (θ * C0 * exp 1) ^ m := by
  let q : ℝ := ((2 * m + 1 : ℕ) : ℝ) / C0
  let s : ℝ := sqrt q
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hq_nonneg : 0 ≤ q := hq_pos.le
  have hs_pos : 0 < s := by
    dsimp [s]
    exact sqrt_pos.mpr hq_pos
  have hs_pow : s ^ (2 * m) = q ^ m := by
    dsimp [s]
    rw [pow_mul, sq_sqrt hq_nonneg]
  have hs_sq : s ^ 2 = q := by
    dsimp [s]
    rw [sq_sqrt hq_nonneg]
  have hmoment := integral_pow_two_mul_le_of_hasSubgaussianMGF h hs_pos m
  have hterm_eq :
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ =
        (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ := by
    calc ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
        = ∫ ω, (θ ^ m / (Nat.factorial m : ℝ)) * X ω ^ (2 * m) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
      _ = (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ := by
          rw [integral_const_mul]
  rw [hterm_eq]
  have hcoef_nonneg : 0 ≤ θ ^ m / (Nat.factorial m : ℝ) := by
    positivity
  calc (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ
      ≤ (θ ^ m / (Nat.factorial m : ℝ)) *
          ((Nat.factorial (2 * m) : ℝ) / s ^ (2 * m) *
            exp ((c : ℝ) * s ^ 2 / 2)) := by
        exact mul_le_mul_of_nonneg_left hmoment hcoef_nonneg
    _ = θ ^ m *
          (((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m) *
            exp ((c : ℝ) * q / 2) := by
        rw [hs_pow, hs_sq]
        field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
    _ ≤ θ ^ m * C0 ^ m * exp (m + 1 : ℝ) := by
        have hfac := factorial_two_mul_div_factorial_le_succ_pow m
        have hratio :
            ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m
              ≤ C0 ^ m := by
          have hnum_pos : 0 < (((2 * m + 1 : ℕ) : ℝ) ^ m) := by positivity
          have hC0pow_nonneg : 0 ≤ C0 ^ m := by positivity
          calc
            ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m
                = ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) *
                  (C0 ^ m / (((2 * m + 1 : ℕ) : ℝ) ^ m)) := by
                    dsimp [q]
                    rw [div_pow]
                    field_simp [hC0.ne']
            _ ≤ (((2 * m + 1 : ℕ) : ℝ) ^ m) *
                  (C0 ^ m / (((2 * m + 1 : ℕ) : ℝ) ^ m)) := by
                    exact mul_le_mul_of_nonneg_right hfac
                      (div_nonneg hC0pow_nonneg hnum_pos.le)
            _ = C0 ^ m := by
                    field_simp [ne_of_gt hnum_pos]
        have hexp_le : exp ((c : ℝ) * q / 2) ≤ exp (m + 1 : ℝ) := by
          apply exp_le_exp.mpr
          have hc_div_le : (c : ℝ) / C0 ≤ 1 := by
            rw [div_le_one hC0]
            exact hc_le
          have hnon : 0 ≤ ((2 * m + 1 : ℕ) : ℝ) / 2 := by positivity
          calc
            (c : ℝ) * q / 2 =
                ((c : ℝ) / C0) * (((2 * m + 1 : ℕ) : ℝ) / 2) := by
                  dsimp [q]
                  field_simp [hC0.ne']
            _ ≤ 1 * (((2 * m + 1 : ℕ) : ℝ) / 2) :=
                mul_le_mul_of_nonneg_right hc_div_le hnon
            _ ≤ (m + 1 : ℝ) := by
                norm_num
                nlinarith
        calc
          θ ^ m * (((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m) *
              exp ((c : ℝ) * q / 2)
              ≤ θ ^ m * C0 ^ m * exp ((c : ℝ) * q / 2) := by
                gcongr
          _ ≤ θ ^ m * C0 ^ m * exp (m + 1 : ℝ) := by
                gcongr
    _ = exp 1 * (θ * C0 * exp 1) ^ m := by
        rw [show (m + 1 : ℝ) = (m : ℝ) + 1 by norm_num, exp_add]
        rw [show exp (m : ℝ) = exp 1 ^ m by
          rw [show (m : ℝ) = (m : ℝ) * 1 by ring, Real.exp_nat_mul]]
        rw [mul_pow, mul_pow]
        ring

/-- Second moment of a sub-Gaussian variable: `𝔼 X² ≤ e · (C₀ e)` for a proxy `C₀ ≥ c`, `C₀ > 0`.
Atlas `hanson-wright` (helper). -/
theorem integral_sq_le_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {C0 : ℝ}
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0) :
    ∫ ω, X ω ^ 2 ∂μ ≤ exp 1 * (C0 * exp 1) := by
  have hterm :=
    integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h
      (θ := 1) (C0 := C0) (by norm_num) hC0 hc_le 1
  convert hterm using 1 <;> ring_nf

/-- Fourth moment of a sub-Gaussian variable: `𝔼 X⁴ ≤ 2e · (C₀ e)²` for a proxy `C₀ ≥ c`,
`C₀ > 0`. Atlas `hanson-wright` (helper). -/
theorem integral_pow_four_le_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {C0 : ℝ}
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0) :
    ∫ ω, X ω ^ 4 ∂μ ≤ 2 * exp 1 * (C0 * exp 1) ^ 2 := by
  have hterm :=
    integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h
      (θ := 1) (C0 := C0) (by norm_num) hC0 hc_le 2
  have hfac : (Nat.factorial 2 : ℝ) = 2 := by norm_num
  have hterm' : ∫ ω, X ω ^ 4 / 2 ∂μ ≤ exp 1 * (C0 * exp 1) ^ 2 := by
    have hfun :
        (fun ω : Ω => (1 : ℝ) ^ 2 * X ω ^ (2 * 2) /
          (Nat.factorial 2 : ℝ)) =
          (fun ω : Ω => X ω ^ 4 / 2) := by
      funext ω
      norm_num [hfac]
    rw [hfun] at hterm
    simpa only [one_mul] using hterm
  have hscale : ∫ ω, X ω ^ 4 / 2 ∂μ = (1 / 2 : ℝ) * ∫ ω, X ω ^ 4 ∂μ := by
    calc
      ∫ ω, X ω ^ 4 / 2 ∂μ = ∫ ω, (1 / 2 : ℝ) * X ω ^ 4 ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        ring
      _ = (1 / 2 : ℝ) * ∫ ω, X ω ^ 4 ∂μ := by rw [integral_const_mul]
  rw [hscale] at hterm'
  nlinarith

end NLAlib
