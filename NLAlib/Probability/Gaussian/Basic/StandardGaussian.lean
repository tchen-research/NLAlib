import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The standard Gaussian law

* `IsStandardGaussian μ g` (`HasLaw g (gaussianReal 0 1) μ`, an `abbrev`) and
  `aemeasurable_of_isStandardGaussian`;
* `integrable_pow_gaussianReal`, `integral_pow_three_gaussianReal`,
  `integral_pow_four_gaussianReal`: moments of `N(0, 1)`;
* `memLp_two_and_moments_of_isStandardGaussian`: the first four moments of a standard Gaussian
  variable;
* `hasSubgaussianMGF_id_gaussianReal`, `hasSubgaussianMGF_of_isStandardGaussian`: `N(0, v)` is
  sub-Gaussian with variance proxy `v` (exact mgf bound).

Atlas: `scalar-laws-def`, `gaussian-matrix-def` (sub-Gaussian API, audit G1 C9),
`hutchinson-variance` (law-to-moments bridge).
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- `g` has the standard Gaussian law under `μ`: `HasLaw g (gaussianReal 0 1) μ`, i.e. `g` is
a.e.-measurable and `μ.map g = gaussianReal 0 1`. Tropp 2015, §4.1.
atlas: scalar-laws-def -/
abbrev IsStandardGaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : Ω → ℝ) : Prop :=
  HasLaw g (gaussianReal 0 1) μ

/-- A standard Gaussian law already forces a.e. measurability, since the law is nonzero.
Atlas `hutchinson-variance` (law-to-measurability bridge). -/
theorem aemeasurable_of_isStandardGaussian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : Ω → ℝ}
    (hlaw : IsStandardGaussian μ g) : AEMeasurable g μ :=
  hlaw.aemeasurable

/-- Every monomial `x ↦ x^k` is integrable for the standard Gaussian. Atlas:
`gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`gint`). -/
theorem integrable_pow_gaussianReal (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (k : NNReal)).integrable_norm_pow'
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp [norm_pow]

/-- The third moment of a standard Gaussian vanishes: `E X³ = 0` (symmetry). Atlas:
`gaussian-frob-fourth-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.frobenius_fourth_moment` (`gm3`). -/
theorem integral_pow_three_gaussianReal : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = 0 := by
  have h : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = ∫ x, (-x) ^ 3 ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← neg_zero, ← gaussianReal_map_neg (μ := 0) (v := 1)]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have h2 : ∫ x, (-x) ^ 3 ∂(gaussianReal 0 1) = - ∫ x, x ^ 3 ∂(gaussianReal 0 1) := by
    rw [← integral_neg]; congr 1; ext x; ring
  linarith

/-- The fourth moment of a standard Gaussian: `E X⁴ = 3`. Atlas: `gaussian-frob-fourth-moment`
(helper). Ported from Prove2me solution `GaussianMatrix.frobenius_fourth_moment` (`gm4`). -/
theorem integral_pow_four_gaussianReal : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h1 : ∀ x : ℝ, gaussianPDFReal 0 1 x • x ^ 4
      = (fun y : ℝ => (√(2 * Real.pi))⁻¹ * (y ^ (4:ℝ) * Real.exp (-(1/2) * y ^ (2:ℝ)))) |x| := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    have e4 : |x| ^ (4:ℝ) = x ^ 4 := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, pow_abs]
      exact abs_of_nonneg (by positivity)
    have e2 : |x| ^ (2:ℝ) = x ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [e4, e2]; ring_nf
  rw [integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_comp_abs (f := fun y : ℝ =>
      (√(2 * Real.pi))⁻¹ * (y ^ (4:ℝ) * Real.exp (-(1/2) * y ^ (2:ℝ)))),
    integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)]
  have hg : Real.Gamma ((4 + 1) / 2) = 3 / 4 * √Real.pi := by
    have := Real.Gamma_nat_add_one_add_half 1
    norm_num [Nat.doubleFactorial] at this
    rw [show ((4:ℝ) + 1) / 2 = 5 / 2 by norm_num, this]; ring
  rw [hg]
  have hb : (1/2 : ℝ) ^ (-(4 + 1) / 2 : ℝ) = 4 * √2 := by
    rw [show (-(4 + 1) / 2 : ℝ) = -(2 + 1/2) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_add (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, ← Real.sqrt_eq_rpow]
    norm_num
    field_simp
  rw [hb, Real.sqrt_mul (by norm_num)]
  have : (0:ℝ) < √2 := by positivity
  have : (0:ℝ) < √Real.pi := by positivity
  field_simp

/-- A variable with the standard Gaussian law has finite second and fourth moments,
mean zero, second moment one and fourth moment three. Avron–Toledo 2011, Lemma 5;
atlas `hutchinson-variance` (law-to-moments bridge). -/
theorem memLp_two_and_moments_of_isStandardGaussian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g : Ω → ℝ} (hlaw : IsStandardGaussian μ g) :
    MemLp g 2 μ ∧ (∫ ω, g ω ∂μ) = 0 ∧ (∫ ω, g ω ^ 2 ∂μ) = 1 ∧
      Integrable (fun ω => g ω ^ 4) μ ∧ (∫ ω, g ω ^ 4 ∂μ) = 3 := by
  have hg := hlaw.aemeasurable
  replace hlaw := hlaw.map_eq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)
    rw [← hlaw] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id hg).1 h
  · have h := integral_id_gaussianReal (μ := 0) (v := 1)
    rw [← hlaw, integral_map hg (f := fun x : ℝ => x) (by fun_prop)] at h
    simpa using h
  · have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    simp only [id, integral_id_gaussianReal, sub_zero] at h
    rw [← hlaw, integral_map hg (by fun_prop)] at h
    simpa using h
  · have h := integrable_pow_gaussianReal 4
    rw [← hlaw] at h
    exact (integrable_map_measure (by fun_prop) hg).1 h
  · have h := integral_pow_four_gaussianReal
    rw [← hlaw, integral_map hg (by fun_prop)] at h
    exact h

/-- **A centred Gaussian is sub-Gaussian with its variance as proxy**:
`E[exp(t Y)] = exp(v t²/2)` for `Y ∼ N(0, v)`, so `HasSubgaussianMGF id v (gaussianReal 0 v)`
(with equality in the mgf bound).

Vershynin 2018, §2.5, Example 2.5.8(i) (there in `ψ₂`-norm form; here the exact mgf form);
proof from Mathlib `mgf_id_gaussianReal`. Atlas: `gaussian-matrix-def` (sub-Gaussian API, audit G1 C9).
Also the standard-Gaussian case `v = 1` used by the Hanson–Wright proof.
atlas: gaussian-matrix-def -/
theorem hasSubgaussianMGF_id_gaussianReal (v : NNReal) :
    HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := by
    simpa only [id_eq] using integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp only [zero_mul, zero_add, le_refl]

/-- A standard Gaussian variable is sub-Gaussian with variance proxy `1`.
Source: Vershynin (2018), Example 2.5.8(i). Atlas: `hutchinson-tail` (helper). -/
theorem hasSubgaussianMGF_of_isStandardGaussian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g : Ω → ℝ} (hg : IsStandardGaussian μ g) :
    HasSubgaussianMGF g 1 μ := by
  have hm : AEMeasurable g μ := aemeasurable_of_isStandardGaussian hg
  rw [← HasSubgaussianMGF.id_map_iff hm, hg.map_eq]
  exact hasSubgaussianMGF_id_gaussianReal 1

end NLAlib
