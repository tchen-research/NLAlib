import NLAlib.Probability.ChiSquare.ChiSquare
import NLAlib.Matrix.Norms.Core
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Gaussian chi-square domination from directional sub-Gaussian proxies

Nonnegative Gaussian linearization and Tonelli compare the squared-norm MGF on any
probability space for a random vector with
directional sub-Gaussian proxies to the standard Gaussian chi-square MGF, giving the
chi-square Chernoff and Laurent–Massart tails for such a vector. This is the additive row
flattening input for the one-sign SRHT (atlas `srht-ose`). Laurent–Massart 2000, Lemma 1;
Tropp 2011 (SRHT row norms).
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal
namespace NLAlib

/-- The exponential integral of a standard Gaussian linear form: `𝔼 e^{a ⬝ g} = e^{‖a‖₂² / 2}`
for `g ∼ gaussianVector (Fin d)`. -/
theorem integral_exp_dotProduct_gaussianVector {d : ℕ} (a : Fin d → ℝ) :
    ∫ g : Fin d → ℝ, Real.exp (a ⬝ᵥ g) ∂(gaussianVector (Fin d)) =
      Real.exp (‖WithLp.toLp 2 a‖ ^ 2 / 2) := by
  rw [norm_toLp_sq_eq_dotProduct_self]
  have hs : ∀ t : ℝ, ∫ x : ℝ, Real.exp (t * x) ∂gaussianReal 0 1 = Real.exp (t ^ 2 / 2) := by
    intro t
    simpa only [mgf, id_eq, zero_mul, NNReal.coe_one, one_mul, zero_add] using
      congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [dotProduct, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Real.exp (a i * x))]
  simp_rw [hs]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_div]
  simp only [pow_two]

/-- Gaussian linearization: `e^{θ ‖v‖₂²} = 𝔼 e^{√(2θ) (g ⬝ v)}` for `g ∼ gaussianVector (Fin d)`,
including `θ = 0`. -/
theorem integral_exp_sqrt_mul_dotProduct_gaussianVector {d : ℕ}
    (v : Fin d → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ g : Fin d → ℝ, Real.exp (Real.sqrt (2 * θ) * (g ⬝ᵥ v))
        ∂(gaussianVector (Fin d)) = Real.exp (θ * ‖WithLp.toLp 2 v‖ ^ 2) := by
  have heq : (fun g : Fin d → ℝ => Real.exp (Real.sqrt (2 * θ) * (g ⬝ᵥ v))) =
      (fun g => Real.exp ((Real.sqrt (2 * θ) • v) ⬝ᵥ g)) := by
    funext g
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm g v]
  rw [heq, integral_exp_dotProduct_gaussianVector, norm_toLp_sq_eq_dotProduct_self,
    norm_toLp_sq_eq_dotProduct_self, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  congr 1
  have hs := Real.sq_sqrt (show 0 ≤ 2 * θ by positivity)
  rw [← mul_assoc, ← sq, hs]
  ring

/-- Directional sub-Gaussian hypotheses imply almost-everywhere measurability of the vector.
It suffices to evaluate them in the coordinate directions. -/
theorem aemeasurable_of_directional_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : ℕ} {X : Ω → Fin d → ℝ}
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) μ) : AEMeasurable X μ := by
  apply aemeasurable_pi_lambda
  intro i
  simpa using (hmgf (Pi.single i 1)).aemeasurable

/-- Nonnegative Gaussian linearization and Tonelli bound the squared-norm exponential
integral under an arbitrary probability measure by the chi-square MGF.
Source: Tropp (2011), Lemma 3.3, directional sub-Gaussian version. -/
theorem lintegral_exp_sq_norm_le_chi_square_mgf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1 / 2) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) ∂μ) ≤
      ENNReal.ofReal ((1 - 2 * θ) ^ (-((d : ℝ) / 2))) := by
  simp only [norm_toLp_sq_eq_dotProduct_self]
  let γ := gaussianVector (Fin d)
  let F : Ω → (Fin d → ℝ) → ℝ := fun ω g =>
    Real.exp (Real.sqrt (2 * θ) * (g ⬝ᵥ X ω))
  have hXm := aemeasurable_of_directional_hasSubgaussianMGF hmgf
  have hcoord (i : Fin d) : AEMeasurable (fun ω => X ω i) μ :=
    aemeasurable_pi_iff.mp hXm i
  have hFmeas : AEMeasurable (Function.uncurry F) (μ.prod γ) := by
    have hcoord' (i : Fin d) : AEMeasurable
        (fun z : Ω × (Fin d → ℝ) => X z.1 i) (μ.prod γ) := (hcoord i).comp_fst
    dsimp [Function.uncurry, F, dotProduct]
    apply AEMeasurable.exp
    apply AEMeasurable.const_mul
    exact Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
      (((measurable_pi_apply i).comp measurable_snd).aemeasurable.mul (hcoord' i))
  have hlin (v : Fin d → ℝ) :
      (∫ g, Real.exp (Real.sqrt (2 * θ) * (g ⬝ᵥ v)) ∂γ) =
        Real.exp (θ * (v ⬝ᵥ v)) := by
    rw [integral_exp_sqrt_mul_dotProduct_gaussianVector v hθ0, norm_toLp_sq_eq_dotProduct_self]
  have hF (ω : Ω) : Integrable (F ω) γ := by
    apply Integrable.of_integral_ne_zero
    rw [show (∫ g, F ω g ∂γ) = Real.exp (θ * (X ω ⬝ᵥ X ω)) from hlin (X ω)]
    exact (Real.exp_pos _).ne'
  have hgauss : (∫ g : Fin d → ℝ, Real.exp (θ * (g ⬝ᵥ g)) ∂γ) =
      (1 - 2 * θ) ^ (-((d : ℝ) / 2)) := by
    have hh := integral_exp_neg_mul_sum_sq_gaussianVector (ι := Fin d) (1 - 2 * θ)
      (show 0 < 1 - 2 * θ by linarith)
    rw [show -((1 - 2 * θ - 1) / 2) = θ by ring, Fintype.card_fin] at hh
    simpa only [dotProduct, ← sq] using hh
  have hgint : Integrable (fun g : Fin d → ℝ => Real.exp (θ * (g ⬝ᵥ g))) γ :=
    Integrable.of_integral_ne_zero (by rw [hgauss]; exact
      (Real.rpow_pos_of_pos (show 0 < 1 - 2 * θ by linarith) _).ne')
  have hsection (g : Fin d → ℝ) : Integrable (fun ω => F ω g) μ ∧
      (∫ ω, F ω g ∂μ) ≤ Real.exp (θ * (g ⬝ᵥ g)) := by
    let u := Real.sqrt (2 * θ) • g
    have hsu := hmgf u
    have heu : ((‖WithLp.toLp 2 u‖₊ ^ 2 : ℝ≥0) : ℝ) / 2 = θ * (g ⬝ᵥ g) := by
      rw [NNReal.coe_pow, coe_nnnorm, norm_toLp_sq_eq_dotProduct_self]
      dsimp only [u]
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      rw [← mul_assoc, ← sq, Real.sq_sqrt (show 0 ≤ 2 * θ by positivity)]
      ring
    have heq : (fun ω => Real.exp (1 * (X ω ⬝ᵥ u))) = (fun ω => F ω g) := by
      funext ω
      simp only [u, F, one_mul, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    constructor
    · simpa only [heq] using hsu.integrable_exp_mul 1
    · have hh := hsu.mgf_le 1
      rw [mgf, heq] at hh
      simp only [one_pow, mul_one] at hh
      change (∫ ω, F ω g ∂μ) ≤
        Real.exp (((‖WithLp.toLp 2 u‖₊ ^ 2 : ℝ≥0) : ℝ) / 2) at hh
      rwa [heu] at hh
  calc
    _ = ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (F ω g) ∂γ ∂μ := by
      apply lintegral_congr
      intro ω
      rw [← ofReal_integral_eq_lintegral_ofReal (hF ω)
        (Filter.Eventually.of_forall fun g => (Real.exp_pos _).le), hlin (X ω)]
    _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (F ω g) ∂μ ∂γ :=
      lintegral_lintegral_swap hFmeas.ennreal_ofReal
    _ ≤ ∫⁻ g, ENNReal.ofReal (Real.exp (θ * (g ⬝ᵥ g))) ∂γ := by
      apply lintegral_mono
      intro g
      change (∫⁻ ω, ENNReal.ofReal (F ω g) ∂μ) ≤
        ENNReal.ofReal (Real.exp (θ * (g ⬝ᵥ g)))
      rw [← ofReal_integral_eq_lintegral_ofReal (hsection g).1
        (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal (hsection g).2
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hgint
        (Filter.Eventually.of_forall fun g => (Real.exp_pos _).le), hgauss]

/-- The finite Gaussian MGF bound implies integrability of the squared-norm exponential.
Source: Tropp (2011), Lemma 3.3, Gaussian linearization. -/
theorem integrable_exp_sq_norm_of_directional_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1 / 2) :
    Integrable (fun ω => Real.exp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) μ := by
  have hXm := aemeasurable_of_directional_hasSubgaussianMGF hmgf
  have hc (i : Fin d) : AEMeasurable (fun ω => X ω i) μ :=
    aemeasurable_pi_iff.mp hXm i
  have hm : AEMeasurable (fun ω => Real.exp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) μ := by
    simp only [norm_toLp_sq_eq_dotProduct_self, dotProduct]
    apply AEMeasurable.exp
    apply AEMeasurable.const_mul
    exact Finset.aemeasurable_fun_sum Finset.univ fun i _ => (hc i).mul (hc i)
  refine ⟨hm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).2 ?_⟩
  exact (lintegral_exp_sq_norm_le_chi_square_mgf μ X hmgf hθ0 hθ1).trans_lt (by simp)

/-- A random vector with directional sub-Gaussian proxy `‖u‖₂²` has squared-norm MGF
at most `(1−2θ)^(-d/2)` for `0 ≤ θ < 1/2`, on any probability space.
Source: Tropp (2011), Lemma 3.3, directional sub-Gaussian version. -/
theorem integral_exp_sq_norm_le_chi_square_mgf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1 / 2) :
    (∫ ω, Real.exp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2) ∂μ) ≤
      (1 - 2 * θ) ^ (-((d : ℝ) / 2)) := by
  have hpos := Real.rpow_pos_of_pos (show 0 < 1 - 2 * θ by linarith) (-((d : ℝ) / 2))
  rw [← ENNReal.ofReal_le_ofReal_iff hpos.le,
    ofReal_integral_eq_lintegral_ofReal (integrable_exp_sq_norm_of_directional_hasSubgaussianMGF μ X hmgf hθ0 hθ1)
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  exact lintegral_exp_sq_norm_le_chi_square_mgf μ X hmgf hθ0 hθ1


/-- The squared-norm tail of a random vector with directional sub-Gaussian proxies has
the chi-square Chernoff bound `P(‖X‖² ≥ u) ≤ e^{-θ u} (1 − 2θ)^{-d/2}`. Tropp 2011, Lemma 3.3. -/
theorem measureReal_sq_norm_ge_le_chi_square_mgf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) μ)
    (u θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1 / 2) :
    μ.real {ω | u ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (-θ * u) * (1 - 2 * θ) ^ (-((d : ℝ) / 2)) := by
  have hh := measure_ge_le_exp_mul_mgf (μ := μ)
    (X := fun ω => ‖WithLp.toLp 2 (X ω)‖ ^ 2) u hθ0 (integrable_exp_sq_norm_of_directional_hasSubgaussianMGF μ X hmgf hθ0 hθ1)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact integral_exp_sq_norm_le_chi_square_mgf μ X hmgf hθ0 hθ1

/-- Optimised Chernoff tail for a random vector with directional sub-Gaussian proxies:
`P(‖X‖² ≥ (1 + ε) d) ≤ exp(−(d/2)(ε − log(1 + ε)))`. Dasgupta–Gupta 2003, Lemma 2.2(b) form. -/
theorem measureReal_sq_norm_ge_one_add_mul_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | (1 + ε) * d ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (-((d : ℝ) / 2) * (ε - Real.log (1 + ε))) := by
  have h1ε : 0 < 1 + ε := by linarith
  let θ := ε / (2 * (1 + ε))
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 / 2 := by
    dsimp only [θ]
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have h2 : 1 - 2 * θ = (1 + ε)⁻¹ := by dsimp only [θ]; field_simp; ring
  refine (measureReal_sq_norm_ge_le_chi_square_mgf μ X hmgf ((1 + ε) * d) θ hθ0 hθ1).trans
    (le_of_eq ?_)
  rw [h2, Real.inv_rpow h1ε.le, ← Real.rpow_neg h1ε.le, neg_neg, Real.rpow_def_of_pos h1ε,
    ← Real.exp_add]
  congr 1
  dsimp only [θ]
  field_simp
  ring

/-- Laurent–Massart's additive upper tail `P(‖X‖² ≥ d + 2√(d x) + 2x) ≤ e^{-x}` for a
random vector with directional sub-Gaussian proxies, by Gaussian linearization.
Laurent–Massart 2000, Lemma 1. -/
theorem measureReal_sq_norm_ge_add_two_sqrt_mul_add_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | d + 2 * Real.sqrt (d * x) + 2 * x ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (-x) := by
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ofReal_measureReal]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rcases hx.eq_or_lt with rfl | hx0
    · rw [neg_zero, Real.exp_zero, ENNReal.ofReal_one]
      exact prob_le_one
    · have heq : {ω | ((0 : ℕ) : ℝ) + 2 * Real.sqrt (((0 : ℕ) : ℝ) * x) + 2 * x ≤
          ‖WithLp.toLp 2 (X ω)‖ ^ 2} = ∅ := by
        ext ω
        simp only [norm_toLp_sq_eq_dotProduct_self, dotProduct, Finset.univ_eq_empty,
          Finset.sum_empty, Nat.cast_zero, zero_mul, Real.sqrt_zero, mul_zero, zero_add,
          Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        linarith
      rw [heq, measure_empty]
      exact zero_le
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  let a := Real.sqrt (x / d)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = x / d := Real.sq_sqrt (by positivity)
  have hsqrt : Real.sqrt ((d : ℝ) * x) = d * a := by
    rw [show (d : ℝ) * x = (d : ℝ) ^ 2 * (x / d) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hd0.le]
  have hthreshold : (d : ℝ) + 2 * Real.sqrt (d * x) + 2 * x =
      (1 + (2 * a + 2 * a ^ 2)) * d := by
    rw [hsqrt, ha2]
    field_simp
    ring
  rw [hthreshold]
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ((measureReal_sq_norm_ge_one_add_mul_le μ X hmgf
    (by positivity)).trans (Real.exp_le_exp.mpr ?_))
  have hlog : Real.log (1 + (2 * a + 2 * a ^ 2)) ≤ 2 * a := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have hh := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * a by positivity)
    nlinarith
  have hx' : x = a ^ 2 * d := by rw [ha2]; field_simp
  rw [hx']
  nlinarith


/-- The squared-norm MGF comparison specializes to a PMF on any sample type. -/
theorem integral_exp_sq_norm_le_chi_square_mgf_pmf
    {Ω : Type*} [MeasurableSpace Ω] (p : PMF Ω) {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) p.toMeasure)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1 / 2) :
    (∫ ω, Real.exp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2) ∂p.toMeasure) ≤
      (1 - 2 * θ) ^ (-((d : ℝ) / 2)) :=
  integral_exp_sq_norm_le_chi_square_mgf p.toMeasure X hmgf hθ0 hθ1

/-- The squared-norm Chernoff bound specializes to a PMF on any sample type. -/
theorem measureReal_sq_norm_ge_le_chi_square_mgf_pmf
    {Ω : Type*} [MeasurableSpace Ω] (p : PMF Ω) {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) p.toMeasure)
    (u θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1 / 2) :
    p.toMeasure.real {ω | u ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (-θ * u) * (1 - 2 * θ) ^ (-((d : ℝ) / 2)) :=
  measureReal_sq_norm_ge_le_chi_square_mgf p.toMeasure X hmgf u θ hθ0 hθ1

/-- The optimized squared-norm Chernoff bound specializes to a PMF on any sample type. -/
theorem measureReal_sq_norm_ge_one_add_mul_le_pmf
    {Ω : Type*} [MeasurableSpace Ω] (p : PMF Ω) {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) p.toMeasure)
    {ε : ℝ} (hε : 0 ≤ ε) :
    p.toMeasure.real {ω | (1 + ε) * d ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (-((d : ℝ) / 2) * (ε - Real.log (1 + ε))) :=
  measureReal_sq_norm_ge_one_add_mul_le p.toMeasure X hmgf hε

/-- Laurent–Massart's additive upper tail specializes to a PMF on any sample type. -/
theorem measureReal_sq_norm_ge_add_two_sqrt_mul_add_le_pmf
    {Ω : Type*} [MeasurableSpace Ω] (p : PMF Ω) {d : ℕ} (X : Ω → Fin d → ℝ)
    (hmgf : ∀ u : Fin d → ℝ, HasSubgaussianMGF (fun ω => X ω ⬝ᵥ u)
      (‖WithLp.toLp 2 u‖₊ ^ 2) p.toMeasure)
    {x : ℝ} (hx : 0 ≤ x) :
    p.toMeasure.real {ω | d + 2 * Real.sqrt (d * x) + 2 * x ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (-x) :=
  measureReal_sq_norm_ge_add_two_sqrt_mul_add_le p.toMeasure X hmgf hx

end NLAlib
