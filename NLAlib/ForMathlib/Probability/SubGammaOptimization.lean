import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sharp scalar optimization of a dimension-prefactored sub-gamma MGF

The square-root plus linear threshold follows from the actual exponential
moment bound. Strict events preserve the endpoint with zero variance and zero
scale. Source: the scalar optimization in Tropp's Gaussian-proxy comparison.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology

namespace NLAlib

private theorem subgamma_parameter {a V c : ℝ} (ha : 0 < a) (hV : 0 < V) (hc : 0 ≤ c) :
    ∃ θ : ℝ, 0 < θ ∧ c * θ < 1 ∧
      a + V * θ ^ 2 / (2 * (1 - c * θ)) = θ * (sqrt (2 * V * a) + c * a) := by
  let q := sqrt (2 * V * a)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqsq : q ^ 2 = 2 * V * a := sq_sqrt (by positivity)
  let D := q + 2 * c * a
  have hD : 0 < D := by dsimp [D]; positivity
  let θ := 2 * a / D
  have hθ : 0 < θ := div_pos (by positivity) hD
  have hdom : c * θ < 1 := by
    dsimp [θ]
    rw [← mul_div_assoc, div_lt_one hD]
    dsimp [D]
    linarith
  refine ⟨θ, hθ, hdom, ?_⟩
  have hid : 1 - c * θ = q / D := by dsimp [θ, D]; field_simp; ring
  rw [hid]
  change a + V * (2 * a / D) ^ 2 / (2 * (q / D)) =
    (2 * a / D) * (q + c * a)
  field_simp [hD.ne', hq.ne']
  dsimp [D]
  nlinarith

/-- The exact Chernoff exponent corresponding to any parameter in the original
sub-gamma moment domain. A prefactor need not be a probability measure mass. -/
theorem measureReal_ge_le_of_subgamma_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {m d V c θ t : ℝ} (hθ : 0 ≤ θ)
    (hexp : Integrable (fun ω => exp (θ * (X ω - m))) μ)
    (hmgf : (∫ ω, exp (θ * (X ω - m)) ∂μ) ≤
      d * exp (V * θ ^ 2 / (2 * (1 - c * θ)))) :
    μ.real {ω | m + t ≤ X ω} ≤
      d * exp (-θ * t + V * θ ^ 2 / (2 * (1 - c * θ))) := by
  have h := measure_ge_le_exp_mul_mgf (X := fun ω => X ω - m) t hθ hexp
  have hset : {ω | m + t ≤ X ω} = {ω | t ≤ X ω - m} := by
    ext ω
    change m + t ≤ X ω ↔ t ≤ X ω - m
    constructor <;> intro h <;> linarith
  rw [hset]
  apply h.trans
  change exp (-θ * t) * (∫ ω, exp (θ * (X ω - m)) ∂μ) ≤ _
  calc
    _ ≤ exp (-θ * t) * (d * exp (V * θ ^ 2 / (2 * (1 - c * θ)))) :=
      mul_le_mul_of_nonneg_left hmgf (exp_pos _).le
    _ = _ := by rw [← mul_assoc, mul_comm (exp _) d, mul_assoc, ← exp_add]

private theorem ae_le_of_bounded_positive_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {m d : ℝ}
    (hexp : ∀ θ : ℝ, 0 ≤ θ → Integrable (fun ω => exp (θ * (X ω - m))) μ)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → (∫ ω, exp (θ * (X ω - m)) ∂μ) ≤ d) :
    ∀ᵐ ω ∂μ, X ω ≤ m := by
  apply (ae_le_const_iff_forall_gt_measure_zero X m).mpr
  intro b hb
  apply (measureReal_eq_zero_iff (μ := μ) (s := {ω | b ≤ X ω}) (by finiteness)).mp
  apply le_antisymm _ measureReal_nonneg
  have hinfty : Tendsto (fun θ : ℝ => -θ * (b - m)) atTop atBot := by
    convert! tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop (sub_pos.mpr hb)) using 1
    funext θ
    dsimp only [Function.comp_apply, id_eq]
    ring
  have hlim : Tendsto (fun θ : ℝ => d * exp (-θ * (b - m))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_atBot.comp hinfty).const_mul d
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with θ hθ
  have hh := measureReal_ge_le_of_subgamma_mgf (V := 0) (c := 0)
    (t := b - m) hθ (hexp θ hθ) (by simpa using hmgf θ hθ)
  simpa only [add_sub_cancel, zero_mul, zero_div, sub_zero, add_zero] using hh

/-- The sharp sub-gamma upper tail when the variance parameter is positive.
The dimension prefactor is retained exactly. -/
theorem measureReal_ge_sqrt_add_le_of_subgamma_mgf_pos
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {m d V c : ℝ} (hV : 0 < V) (hc : 0 ≤ c)
    (hexp : ∀ θ : ℝ, 0 ≤ θ → c * θ < 1 →
      Integrable (fun ω => exp (θ * (X ω - m))) μ)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → c * θ < 1 →
      (∫ ω, exp (θ * (X ω - m)) ∂μ) ≤ d * exp (V * θ ^ 2 / (2 * (1 - c * θ))))
    {s : ℝ} (hs : 0 < s) :
    μ.real {ω | m + sqrt (2 * V * s) + c * s ≤ X ω} ≤ d * exp (-s) := by
  obtain ⟨θ, hθ, hdom, hopt⟩ := subgamma_parameter hs hV hc
  have heq : -θ * (sqrt (2 * V * s) + c * s) +
      V * θ ^ 2 / (2 * (1 - c * θ)) = -s := by linarith
  have hh := measureReal_ge_le_of_subgamma_mgf hθ.le (hexp θ hθ.le hdom)
    (hmgf θ hθ.le hdom) (t := sqrt (2 * V * s) + c * s)
  simpa only [heq, add_assoc] using hh

private theorem measureReal_ge_le_of_zero_variance_subgamma_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {m d c s : ℝ} (hc : 0 < c)
    (hexp : ∀ θ : ℝ, 0 ≤ θ → c * θ < 1 →
      Integrable (fun ω => exp (θ * (X ω - m))) μ)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → c * θ < 1 →
      (∫ ω, exp (θ * (X ω - m)) ∂μ) ≤ d) :
    μ.real {ω | m + c * s ≤ X ω} ≤ d * exp (-s) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  let θ : ℕ → ℝ := fun n => (1 - ε n) / c
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlt (n : ℕ) : ε n < 1 := by
    dsimp [ε]
    rw [div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hθpos (n : ℕ) : 0 ≤ θ n := div_nonneg (sub_nonneg.mpr (hεlt n).le) hc.le
  have hdom (n : ℕ) : c * θ n < 1 := by
    have heq : c * θ n = 1 - ε n := by dsimp [θ]; field_simp
    rw [heq]
    linarith [hεpos n]
  have hbound (n : ℕ) : μ.real {ω | m + c * s ≤ X ω} ≤ d * exp (-θ n * (c * s)) := by
    have hh := measureReal_ge_le_of_subgamma_mgf (V := 0) (c := c) (t := c * s)
      (hθpos n) (hexp (θ n) (hθpos n) (hdom n))
      (by simpa using hmgf (θ n) (hθpos n) (hdom n))
    simpa only [zero_mul, zero_div, add_zero] using hh
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hθlim : Tendsto θ atTop (𝓝 (1 / c)) := by
    simpa only [θ, sub_zero] using (tendsto_const_nhds.sub hεlim).div_const c
  have heq : -(1 / c) * (c * s) = -s := by field_simp
  have hlim : Tendsto (fun n => d * exp (-θ n * (c * s))) atTop (𝓝 (d * exp (-s))) := by
    have hh := (Real.continuous_exp.tendsto (-(1 / c) * (c * s))).comp
      (hθlim.neg.mul_const (c * s))
    simpa only [heq, Function.comp_def] using hh.const_mul d
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)

/-- The sharp strict upper tail from a dimension-prefactored sub-gamma MGF.
All zero parameters are included: when both variance and scale vanish the
positive MGF bound forces `X ≤ m` almost surely, which requires a strict event.
Source: Tropp's Gaussian-proxy comparison, scalar Chernoff optimization. -/
theorem measureReal_gt_sqrt_add_le_of_subgamma_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {m d V c : ℝ} (hd : 1 ≤ d) (hV : 0 ≤ V) (hc : 0 ≤ c)
    (hexp : ∀ θ : ℝ, 0 ≤ θ → c * θ < 1 →
      Integrable (fun ω => exp (θ * (X ω - m))) μ)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → c * θ < 1 →
      (∫ ω, exp (θ * (X ω - m)) ∂μ) ≤ d * exp (V * θ ^ 2 / (2 * (1 - c * θ))))
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | m + sqrt (2 * V * s) + c * s < X ω} ≤ d * exp (-s) := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · simpa only [neg_zero, exp_zero, mul_one] using measureReal_le_one.trans hd
  rcases eq_or_lt_of_le hV with rfl | hV
  · rcases eq_or_lt_of_le hc with rfl | hc
    · have hae := ae_le_of_bounded_positive_mgf
        (fun θ hθ => hexp θ hθ (by simp))
        (fun θ hθ => by simpa using hmgf θ hθ (by simp))
      have hz : μ {ω | m < X ω} = 0 := by simpa only [not_le] using ae_iff.mp hae
      have hzr : μ.real {ω | m < X ω} = 0 := (measureReal_eq_zero_iff (by finiteness)).mpr hz
      simp only [mul_zero, zero_mul, sqrt_zero, add_zero, hzr]
      exact mul_nonneg (by linarith) (exp_pos _).le
    · simp only [mul_zero, zero_mul, sqrt_zero, add_zero]
      have hmono : μ.real {ω | m + c * s < X ω} ≤ μ.real {ω | m + c * s ≤ X ω} :=
        measureReal_mono (by
          intro ω h
          change m + c * s ≤ X ω
          exact (show m + c * s < X ω from h).le)
      exact hmono.trans (measureReal_ge_le_of_zero_variance_subgamma_mgf hc hexp
        (fun θ hθ hdom => by simpa using hmgf θ hθ hdom) (s := s))
  · have hmono : μ.real {ω | m + sqrt (2 * V * s) + c * s < X ω} ≤
        μ.real {ω | m + sqrt (2 * V * s) + c * s ≤ X ω} :=
      measureReal_mono (by
        intro ω h
        change m + sqrt (2 * V * s) + c * s ≤ X ω
        exact (show m + sqrt (2 * V * s) + c * s < X ω from h).le)
    exact hmono.trans (measureReal_ge_sqrt_add_le_of_subgamma_mgf_pos hV hc hexp hmgf hs)

/-- The same sharp tail holds for a non-strict event whenever the variance or
scale parameter is positive, including a zero deviation. -/
theorem measureReal_ge_sqrt_add_le_of_subgamma_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {m d V c : ℝ} (hd : 1 ≤ d) (hV : 0 ≤ V) (hc : 0 ≤ c)
    (hnd : 0 < V ∨ 0 < c)
    (hexp : ∀ θ : ℝ, 0 ≤ θ → c * θ < 1 →
      Integrable (fun ω => exp (θ * (X ω - m))) μ)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → c * θ < 1 →
      (∫ ω, exp (θ * (X ω - m)) ∂μ) ≤ d * exp (V * θ ^ 2 / (2 * (1 - c * θ))))
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | m + sqrt (2 * V * s) + c * s ≤ X ω} ≤ d * exp (-s) := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · simpa only [neg_zero, exp_zero, mul_one] using measureReal_le_one.trans hd
  rcases eq_or_lt_of_le hV with rfl | hV
  · have hcpos : 0 < c := hnd.resolve_left (by simp)
    simpa only [mul_zero, zero_mul, sqrt_zero, add_zero] using
      measureReal_ge_le_of_zero_variance_subgamma_mgf hcpos hexp
        (fun θ hθ hdom => by simpa using hmgf θ hθ hdom) (s := s)
  · exact measureReal_ge_sqrt_add_le_of_subgamma_mgf_pos hV hc hexp hmgf hs

private theorem le_sqrt_add_of_subgamma_dual {x a V c : ℝ}
    (ha : 0 ≤ a) (hV : 0 ≤ V) (hc : 0 ≤ c)
    (hdual : ∀ θ : ℝ, 0 < θ → c * θ < 1 →
      θ * x ≤ a + V * θ ^ 2 / (2 * (1 - c * θ))) :
    x ≤ sqrt (2 * V * a) + c * a := by
  have happrox (δ : ℝ) (hδ : 0 < δ) :
      x ≤ sqrt (2 * (V + δ) * (a + δ)) + c * (a + δ) := by
    obtain ⟨θ, hθ, hdom, hopt⟩ := subgamma_parameter (by linarith : 0 < a + δ)
      (by linarith : 0 < V + δ) hc
    have hden : 0 < 2 * (1 - c * θ) := by linarith
    have hfrac : V * θ ^ 2 / (2 * (1 - c * θ)) ≤
        (V + δ) * θ ^ 2 / (2 * (1 - c * θ)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hδ.le) (sq_nonneg θ)) hden.le
    have hh := hdual θ hθ hdom
    exact le_of_mul_le_mul_left (show θ * x ≤
      θ * (sqrt (2 * (V + δ) * (a + δ)) + c * (a + δ)) by linarith) hθ
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont : Continuous (fun δ : ℝ => sqrt (2 * (V + δ) * (a + δ)) + c * (a + δ)) := by fun_prop
  have hlim : Tendsto (fun n => sqrt (2 * (V + ε n) * (a + ε n)) + c * (a + ε n))
      atTop (𝓝 (sqrt (2 * V * a) + c * a)) := by
    simpa only [Function.comp_def, add_zero] using (hcont.tendsto 0).comp hεlim
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Eventually.of_forall fun n => happrox (ε n) (by dsimp [ε]; positivity))

/-- An integrable real random variable satisfying the actual sub-gamma MGF
bound has the sharp mean bound, including `d = 1`, zero variance and zero
scale. Integrability of `X` is needed because a positive MGF alone does not
control its negative first moment.
Source: Tropp's Gaussian-proxy comparison, scalar Laplace optimization. -/
theorem integral_le_sqrt_log_add_of_subgamma_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) {m d V c : ℝ}
    (hd : 1 ≤ d) (hV : 0 ≤ V) (hc : 0 ≤ c)
    (hexp : ∀ θ : ℝ, 0 ≤ θ → c * θ < 1 →
      Integrable (fun ω => exp (θ * (X ω - m))) μ)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → c * θ < 1 →
      (∫ ω, exp (θ * (X ω - m)) ∂μ) ≤ d * exp (V * θ ^ 2 / (2 * (1 - c * θ)))) :
    (∫ ω, X ω ∂μ) ≤ m + sqrt (2 * V * log d) + c * log d := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hbound : (∫ ω, X ω ∂μ) - m ≤ sqrt (2 * V * log d) + c * log d := by
    apply le_sqrt_add_of_subgamma_dual (log_nonneg hd) hV hc
    intro θ hθ hdom
    have hj := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => mem_univ _))
      ((hX.sub (integrable_const m)).const_mul θ) (hexp θ hθ.le hdom)
    simp only [Pi.sub_apply] at hj
    rw [integral_const_mul, integral_sub hX (integrable_const m),
      integral_const, probReal_univ, one_smul] at hj
    apply exp_le_exp.mp
    exact hj.trans (by simpa only [exp_add, exp_log hdpos] using hmgf θ hθ.le hdom)
  linarith

end NLAlib
