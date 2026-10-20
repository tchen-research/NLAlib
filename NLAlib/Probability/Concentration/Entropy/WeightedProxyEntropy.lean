import NLAlib.Probability.Concentration.Entropy.EntropyTensorization
import Mathlib.Probability.Moments.Basic

/-!
# Entropy duality for an actual random variance proxy

The proxy stays on its actual probability space; it need not be independent
of the exponential test. The first theorem is an integral Gibbs calculation.
The second solves the resulting entropy inequality. Neither theorem assumes
an exponential-moment bound or replaces the random proxy by a constant.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- The actual weighted proxy integral is bounded by entropy plus its actual
logarithmic exponential moment. This is Gibbs variational duality with
`U = θ*V-log(E exp(θ*V))`, whose exponential has integral exactly one. -/
theorem mul_integral_mul_le_entropy_add_mul_log_integral_exp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y V : Ω → ℝ) (hY : ∀ x, 0 < Y x)
    (hYi : Integrable Y μ) (hYlog : Integrable (fun x => Y x * Real.log (Y x)) μ)
    (hYV : Integrable (fun x => Y x * V x) μ)
    {θ : ℝ} (hVi : Integrable (fun x => Real.exp (θ * V x)) μ) :
    θ * (∫ x, Y x * V x ∂μ) ≤
      ((∫ x, Y x * Real.log (Y x) ∂μ) -
        (∫ x, Y x ∂μ) * Real.log (∫ x, Y x ∂μ)) +
      (∫ x, Y x ∂μ) * Real.log (∫ x, Real.exp (θ * V x) ∂μ) := by
  let m : ℝ := ∫ x, Real.exp (θ * V x) ∂μ
  have hm : 0 < m := mgf_pos hVi
  let U : Ω → ℝ := fun x => θ * V x - Real.log m
  have hUeq : (fun x => Real.exp (U x)) =
      (fun x => Real.exp (θ * V x) / m) := by
    ext x
    dsimp [U]
    rw [Real.exp_sub, Real.exp_log hm]
  have hUi : Integrable (fun x => Real.exp (U x)) μ := by
    rw [hUeq]
    exact hVi.div_const m
  have hUone : ∫ x, Real.exp (U x) ∂μ ≤ 1 := by
    rw [hUeq, integral_div]
    change m / m ≤ 1
    rw [div_self hm.ne']
  have hYUi : Integrable (fun x => Y x * U x) μ := by
    convert (hYV.const_mul θ).sub (hYi.mul_const (Real.log m)) using 1
    ext x
    dsimp [U]
    ring
  have hg := integral_mul_le_entropy_of_integral_exp_le_one μ Y U
    hY hYi hYlog hYUi hUi hUone
  have he : ∫ x, Y x * U x ∂μ =
      θ * (∫ x, Y x * V x ∂μ) - (∫ x, Y x ∂μ) * Real.log m := by
    have hfun : (fun x => Y x * U x) =
        (fun x => θ * (Y x * V x) - Y x * Real.log m) := by
      ext x
      dsimp [U]
      ring
    rw [hfun, integral_sub (f := fun x => θ * (Y x * V x))
      (g := fun x => Y x * Real.log m) (hYV.const_mul θ)
      (hYi.mul_const (Real.log m)), integral_const_mul, integral_mul_const]
  rw [he] at hg
  dsimp [m] at hg
  linarith

/-- Solving the actual random-proxy entropy inequality by Gibbs duality.
The only proxy information used on the right is its actual exponential
integral; a separate self-bounding theorem can estimate this quantity. -/
theorem entropy_le_mul_log_integral_exp_of_weighted_proxy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y V : Ω → ℝ) (hY : ∀ x, 0 < Y x)
    (hYi : Integrable Y μ) (hYlog : Integrable (fun x => Y x * Real.log (Y x)) μ)
    (hYV : Integrable (fun x => Y x * V x) μ)
    {θ v : ℝ} (hv : 0 ≤ v) (hθ : v < θ)
    (hVi : Integrable (fun x => Real.exp (θ * V x)) μ)
    (hproxy : (∫ x, Y x * Real.log (Y x) ∂μ) -
      (∫ x, Y x ∂μ) * Real.log (∫ x, Y x ∂μ) ≤
        v * (∫ x, Y x * V x ∂μ)) :
    (∫ x, Y x * Real.log (Y x) ∂μ) -
      (∫ x, Y x ∂μ) * Real.log (∫ x, Y x ∂μ) ≤
      v / (θ - v) * (∫ x, Y x ∂μ) *
        Real.log (∫ x, Real.exp (θ * V x) ∂μ) := by
  have hg := mul_integral_mul_le_entropy_add_mul_log_integral_exp
    μ Y V hY hYi hYlog hYV hVi
  have h := mul_le_mul_of_nonneg_left hg hv
  have hθpos : 0 < θ := hv.trans_lt hθ
  have hp := mul_le_mul_of_nonneg_left hproxy hθpos.le
  have he : v / (θ - v) * (∫ x, Y x ∂μ) *
      Real.log (∫ x, Real.exp (θ * V x) ∂μ) =
      (v * (∫ x, Y x ∂μ) * Real.log (∫ x, Real.exp (θ * V x) ∂μ)) / (θ - v) := by ring
  rw [he]
  apply (le_div_iff₀ (sub_pos.mpr hθ)).mpr
  nlinarith

end NLAlib
