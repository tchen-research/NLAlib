import NLAlib.Probability.Concentration.Matrix.GaussianMaximumMean
import NLAlib.Probability.Concentration.Matrix.GaussianTraceInflation

/-!
# Scalar sub-gamma budget from Gaussian trace comparison

The actual Gaussian weak-variance concentration and mean scale decomposition
convert a trace-MGF replacement inequality into the precise scalar sub-gamma
budget. This interface records the replacement premise explicitly; the
independent-sum theorem discharges it using BMV replacement.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix
namespace NLAlib
variable {n Ω : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- A genuine trace replacement inequality implies the exact centered scalar
sub-gamma MGF budget, with the replacement premise explicitly displayed.
This intermediate result includes zero time, zero weak variance and a zero
upper summand bound. Source: Tropp (2026), Section 4.9.
atlas: gaussian-proxy-eigenvalue-comparison (partial) -/
theorem integrable_exp_mul_lambdaMax_sub_and_integral_le_of_trace_comparison
    (Y : Ω → M) (hY : AEMeasurable Y P) (hYHerm : ∀ᵐ ω ∂P, (Y ω).IsHermitian)
    (D : M) (hD : D.IsHermitian)
    (γ : Measure M) [IsGaussian γ]
    (hHerm : ∀ᵐ Z ∂γ, Z.IsHermitian) (hmean : ∫ Z, Z ∂γ = 0)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hvariance : ∀ u : n → ℂ, ‖WithLp.toLp 2 u‖ = 1 →
      Var[fun Z => (quadForm Z u).re; γ] ≤ σ ^ 2)
    {R θ : ℝ} (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3)
    (htrace : Integrable (fun ω => traceExp (θ • (Y ω + D))) P)
    (hcomparison : (∫ ω, traceExp (θ • (Y ω + D)) ∂P) ≤
      ∫ Z, traceExp (θ • D + gaussianTraceInflation R θ • Z) ∂γ) :
    Integrable (fun ω => Real.exp (θ * (lambdaMax (Y ω + D) -
      ∫ Z, lambdaMax (D + Z) ∂γ))) P ∧
    (∫ ω, Real.exp (θ * (lambdaMax (Y ω + D) -
      ∫ Z, lambdaMax (D + Z) ∂γ)) ∂P) ≤
      (Fintype.card n : ℝ) * Real.exp
        ((σ ^ 2 + R * (∫ Z, lambdaMax Z ∂γ) / 3) * θ ^ 2 /
          (2 * (1 - (R / 3) * θ))) := by
  rcases eq_or_lt_of_le hθ with hzero | hpos
  · rw [← hzero]
    constructor
    · simpa only [zero_mul, Real.exp_zero] using (integrable_const (1 : ℝ) : Integrable _ P)
    · simp only [zero_mul, Real.exp_zero, integral_const, probReal_univ, one_smul,
        zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_div, mul_one]
      exact_mod_cast Fintype.card_pos (α := n)
  let m : ℝ := ∫ Z, lambdaMax (D + Z) ∂γ
  let φ : ℝ := ∫ Z, lambdaMax Z ∂γ
  let g : ℝ := gaussianTraceInflation R θ
  have hm : AEMeasurable (fun ω => lambdaMax (Y ω + D)) P := by
    simpa only [add_comm] using aemeasurable_lambdaMax_add_of_ae_isHermitian D hD hY hYHerm
  have hedom : ∀ᵐ ω ∂P,
      Real.exp (θ * lambdaMax (Y ω + D)) ≤ traceExp (θ • (Y ω + D)) :=
    hYHerm.mono fun ω hω =>
      (exp_mul_lambdaMax_lambdaMin_le_traceExp_smul _ (hω.add hD) θ).2.1 hpos
  have hexp : Integrable (fun ω => Real.exp (θ * lambdaMax (Y ω + D))) P := by
    apply htrace.mono' (Real.measurable_exp.comp_aemeasurable (hm.const_mul θ)).aestronglyMeasurable
    filter_upwards [hedom] with ω hω
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hω
  have hecenter (ω : Ω) : Real.exp (θ * (lambdaMax (Y ω + D) - m)) =
      Real.exp (-θ * m) * Real.exp (θ * lambdaMax (Y ω + D)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcenter : Integrable (fun ω => Real.exp (θ * (lambdaMax (Y ω + D) - m))) P := by
    simp_rw [hecenter]
    exact hexp.const_mul _
  refine ⟨hcenter, ?_⟩
  have hφ : 0 ≤ φ := integral_lambdaMax_gaussian_nonneg γ hHerm hmean hσ hvariance
  have hscale := integral_lambdaMax_smul_add_smul_gaussian_le γ D hD hHerm hmean hσ hvariance
    hθ (le_gaussianTraceInflation hR hθ)
  have hgauss := integral_traceExp_add_smul_gaussian_le_exp_mean γ (θ • D)
    (hD.smul (IsSelfAdjoint.all θ)) hHerm hmean hσ hvariance g
  have hraw := (integral_mono_ae hexp htrace hedom).trans (hcomparison.trans hgauss)
  have hden : 0 < 1 - θ * R / 3 := by linarith
  have hdiff := mul_le_mul_of_nonneg_right (gaussianTraceInflation_sub_le_div hR hθ hθR) hφ
  have hsq := mul_le_mul_of_nonneg_right (gaussianTraceInflation_sq_le_div hθR) (sq_nonneg σ)
  have he : (∫ Z, lambdaMax (θ • D + g • Z) ∂γ) + g ^ 2 * σ ^ 2 / 2 - θ * m ≤
      (σ ^ 2 + R * φ / 3) * θ ^ 2 / (2 * (1 - (R / 3) * θ)) := by
    calc
      _ ≤ (g - θ) * φ + g ^ 2 * σ ^ 2 / 2 := by
        change (∫ Z, lambdaMax (θ • D + g • Z) ∂γ) ≤ θ * m + (g - θ) * φ at hscale
        linarith
      _ ≤ (R * θ ^ 2 / (6 * (1 - θ * R / 3))) * φ +
          (θ ^ 2 / (1 - θ * R / 3)) * σ ^ 2 / 2 := by
        change (g - θ) * φ ≤ _ at hdiff
        change g ^ 2 * σ ^ 2 ≤ _ at hsq
        linarith
      _ = _ := by
        have hden' : 1 - (R / 3) * θ = 1 - θ * R / 3 := by ring
        rw [hden']
        field_simp [hden.ne']
        ring
  change (∫ ω, Real.exp (θ * (lambdaMax (Y ω + D) - m)) ∂P) ≤ _
  simp_rw [hecenter]
  rw [integral_const_mul]
  calc
    _ ≤ Real.exp (-θ * m) * ((Fintype.card n : ℝ) *
        Real.exp ((∫ Z, lambdaMax (θ • D + g • Z) ∂γ) + g ^ 2 * σ ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le
    _ = (Fintype.card n : ℝ) * Real.exp
        ((∫ Z, lambdaMax (θ • D + g • Z) ∂γ) + g ^ 2 * σ ^ 2 / 2 - θ * m) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Nat.cast_nonneg _)

end NLAlib
