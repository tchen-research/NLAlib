import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import NLAlib.ForMathlib.Analysis.Calculus.MeanValue

/-!
# Gaussian integration by parts

Stein's identity for the standard Gaussian and its multivariate form for jointly Gaussian
vectors:

* `integral_mul_eq_integral_deriv_gaussianReal`: `∫ x h(x) dγ = ∫ h'(x) dγ` for `h`
  differentiable with bounded derivative (`γ = N(0,1)`);
* `integral_mul_eq_mul_integral_deriv_gaussianReal`: `∫ x h(x) dN(0,v) = v ∫ h' dN(0,v)` for
  bounded `h` with bounded continuous derivative;
* `integral_mul_eq_sum_covariance_mul_integral`: `𝔼[U G(V)] = ∑ⱼ Cov(U, Vⱼ) 𝔼[∂ⱼG(V)]` for a
  jointly Gaussian `(U, V)` with `U` centred.

Also the integrability facts `integrable_abs_gaussianReal`, `integrable_sq_gaussianReal` used
throughout `NLAlib.Gaussian.Concentration` (the linear-growth bound
`abs_le_abs_add_mul_abs_of_abs_deriv_le` is in `NLAlib.ForMathlib.Analysis.Calculus.MeanValue`).

Atlas: `gaussian-integration-by-parts`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-! ### Integrability under the standard Gaussian -/

/-- `|y|` is integrable for the standard Gaussian. Atlas: `gaussian-integration-by-parts`
(helper). Ported from Prove2me solution `GaussianMatrix.gaussian_ibp_one_dim`. -/
theorem integrable_abs_gaussianReal : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) :=
  (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)).abs

/-- `y²` is integrable for the standard Gaussian. Atlas: `gaussian-integration-by-parts`
(helper). Ported from Prove2me solution `GaussianMatrix.gaussian_ibp_one_dim`. -/
theorem integrable_sq_gaussianReal : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_norm_pow (by norm_num)
  simpa using this

private lemma integrable_gaussianReal_iff (g : ℝ → ℝ) :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [smul_eq_mul]

private lemma gaussianPDFReal_zero_one_eq :
    gaussianPDFReal 0 1 = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  funext x; simp [gaussianPDFReal_def]

private lemma hasDerivAt_gaussianPDFReal_zero_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-(x * gaussianPDFReal 0 1 x)) x := by
  rw [gaussianPDFReal_zero_one_eq]
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-x) x :=
    (((hasDerivAt_pow 2 x).neg).div_const 2).congr_deriv (by norm_num; ring)
  exact ((h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹).congr_deriv (by ring)

/-- The derivative of the centred Gaussian density: `φ_v'(x) = -(x / v) φ_v(x)`.
Atlas: `gaussian-integration-by-parts` (helper). Ported from Prove2me solution
`GaussianMatrix.gaussian_integration_by_parts`. -/
theorem hasDerivAt_gaussianPDFReal_zero (v : NNReal) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-(x / v) * gaussianPDFReal 0 v x) x := by
  have h1 : HasDerivAt (fun x : ℝ => -(x - 0) ^ 2 / (2 * v)) (-(2 * (x - 0)) / (2 * v)) x := by
    have := ((hasDerivAt_id x).sub_const 0).pow 2
    simpa using (this.neg).div_const (2 * (v : ℝ))
  have h2 := (h1.exp).const_mul (√(2 * Real.pi * v))⁻¹
  rw [gaussianPDFReal_def]
  refine h2.congr_deriv ?_
  simp only [sub_zero]
  field_simp

/-! ### One-dimensional Stein identity -/

/-- **Gaussian integration by parts** (Stein's identity) in dimension one: for `h`
differentiable with `|h'| ≤ C`, `∫ x h(x) dγ(x) = ∫ h'(x) dγ(x)` with `γ = N(0,1)`.
Source: Stein 1981, Lemma 1; Vershynin 2018, Lemma 7.2.3 (one-dimensional case). Atlas:
`gaussian-integration-by-parts`. Ported from Prove2me solution
`GaussianMatrix.gaussian_ibp_one_dim`. -/
theorem integral_mul_eq_integral_deriv_gaussianReal (h : ℝ → ℝ) (hh : Differentiable ℝ h)
    (C : ℝ) (hdh : ∀ x, |deriv h x| ≤ C) :
    ∫ x, x * h x ∂(gaussianReal 0 1) = ∫ x, deriv h x ∂(gaussianReal 0 1) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hdh 0)
  set φ := gaussianPDFReal 0 1
  have hhc : Continuous h := hh.continuous
  have hxh : Integrable (fun x => x * h x) (gaussianReal 0 1) := by
    refine Integrable.mono' ((integrable_abs_gaussianReal.const_mul |h 0|).add
      (integrable_sq_gaussianReal.const_mul C)) (by fun_prop) ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := abs_le_abs_add_mul_abs_of_abs_deriv_le h hh C hdh x
    have hx := abs_nonneg x
    simp only [Pi.add_apply]
    rw [← sq_abs x]
    nlinarith
  have hdm : Measurable (deriv h) := measurable_deriv h
  have hdi : Integrable (deriv h) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const C) hdm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hdh x)
  have hhi : Integrable h (gaussianReal 0 1) := by
    refine Integrable.mono' ((integrable_const |h 0|).add
      (integrable_abs_gaussianReal.const_mul C)) hhc.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]; exact abs_le_abs_add_mul_abs_of_abs_deriv_le h hh C hdh x)
  rw [integrable_gaussianReal_iff] at hxh hdi hhi
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  -- integration by parts on the line with `u = h`, `v = -φ`, `v' = x φ`
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := h) (v := fun x => -φ x)
    (u' := deriv h) (v' := fun x => x * φ x)
    (fun x _ => (hh x).hasDerivAt)
    (fun x _ => ((hasDerivAt_gaussianPDFReal_zero_one x).neg).congr_deriv (by ring))
    (by
      have : (h * fun x => x * φ x) = fun x => φ x * (x * h x) := by funext x; simp; ring
      rw [this]; exact hxh)
    (by
      have : (deriv h * fun x => -φ x) = fun x => -(φ x * deriv h x) := by funext x; simp; ring
      rw [this]; exact hdi.neg)
    (by
      have : (h * fun x => -φ x) = fun x => -(φ x * h x) := by funext x; simp; ring
      rw [this]; exact hhi.neg)
  have e1 : (fun x => φ x * (x * h x)) = fun x => h x * (x * φ x) := by funext x; ring
  have e2 : (fun x => φ x * deriv h x) = fun x => -(deriv h x * -φ x) := by funext x; ring
  rw [e1, key, e2, integral_neg]

/-- Stein's identity for a centred Gaussian of variance `v`: for `h` bounded with bounded
continuous derivative `h'`, `∫ x h(x) dN(0,v) = v ∫ h'(x) dN(0,v)` (both sides vanish when
`v = 0`). Source: Stein 1981, Lemma 1. Atlas: `gaussian-integration-by-parts`. Ported from
Prove2me solution `GaussianMatrix.gaussian_integration_by_parts`. -/
theorem integral_mul_eq_mul_integral_deriv_gaussianReal (v : NNReal) (h h' : ℝ → ℝ)
    (hh : ∀ x, HasDerivAt h (h' x) x) (hc : Continuous h') (M M' : ℝ) (hb : ∀ x, |h x| ≤ M)
    (hb' : ∀ x, |h' x| ≤ M') :
    ∫ x, x * h x ∂(gaussianReal 0 v) = v * ∫ x, h' x ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv; simp [gaussianReal_zero_var]
  have hv' : (0 : ℝ) < v := by positivity
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x => (hh x).continuousAt
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  have hφ : Integrable (gaussianPDFReal 0 v) := integrable_gaussianPDFReal 0 v
  have hxφ : Integrable (fun x => x * gaussianPDFReal 0 v x) := by
    have := (integrable_mul_exp_neg_mul_sq (b := 1 / (2 * v)) (by positivity)).const_mul
      (Real.sqrt (2 * Real.pi * v))⁻¹
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [gaussianPDFReal_def, sub_zero]
    ring_nf
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := h) (u' := h')
    (v := gaussianPDFReal 0 v) (v' := fun x => -(x / v) * gaussianPDFReal 0 v x)
    (fun x _ => hh x) (fun x _ => hasDerivAt_gaussianPDFReal_zero v hv x) ?_ ?_ ?_
  · simp only [smul_eq_mul]
    have e1 : ∫ x, h x * (-(x / v) * gaussianPDFReal 0 v x)
        = -(1 / v) * ∫ x, gaussianPDFReal 0 v x * (x * h x) := by
      rw [← integral_const_mul]; congr 1; ext x; ring
    have e2 : ∫ x, h' x * gaussianPDFReal 0 v x = ∫ x, gaussianPDFReal 0 v x * h' x := by
      congr 1; ext x; ring
    rw [e1, e2] at key
    have k2 : (1 / (v:ℝ)) * ∫ x, gaussianPDFReal 0 v x * (x * h x)
        = ∫ x, gaussianPDFReal 0 v x * h' x := by linarith
    rw [← k2]; field_simp
  · have : Integrable (fun x => -(1 / (v : ℝ)) * (x * gaussianPDFReal 0 v x)) := hxφ.const_mul _
    refine Integrable.mono' (this.norm.const_mul M) ?_ (ae_of_all _ fun x => ?_)
    · exact (hhc.mul (by
        have : Continuous (gaussianPDFReal 0 v) := by
          rw [gaussianPDFReal_def]; fun_prop
        fun_prop)).aestronglyMeasurable
    · simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      have := hb x
      rw [abs_neg, abs_neg, abs_div, abs_div, abs_one]
      have e : |x| / |(v:ℝ)| * |gaussianPDFReal 0 v x|
          = 1 / |(v:ℝ)| * (|x| * |gaussianPDFReal 0 v x|) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right this (by positivity)
  · refine Integrable.mono' (hφ.norm.const_mul M') ?_ (ae_of_all _ fun x => ?_)
    · exact (hc.mul (by rw [gaussianPDFReal_def]; fun_prop)).aestronglyMeasurable
    · simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hb' x) (abs_nonneg _)
  · refine Integrable.mono' (hφ.norm.const_mul M) ?_ (ae_of_all _ fun x => ?_)
    · exact (hhc.mul (by rw [gaussianPDFReal_def]; fun_prop)).aestronglyMeasurable
    · simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)

/-! ### Multivariate Gaussian integration by parts -/

/-- For a jointly Gaussian pair `(U, W)` with `U` real and `W` vector-valued, if `U` is
uncorrelated with every coordinate of `W` then `U` and `W` are independent. Atlas:
`gaussian-integration-by-parts` (helper). Ported from Prove2me solution
`GaussianMatrix.gaussian_integration_by_parts`. -/
theorem indepFun_of_hasGaussianLaw_of_covariance_eq_zero {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {P : Measure Ω} (U : Ω → ℝ) (W : ι → Ω → ℝ)
    (hUW : HasGaussianLaw (fun ω => (U ω, fun j => W j ω)) P)
    (hcov : ∀ j, cov[U, W j; P] = 0) :
    IndepFun U (fun ω j => W j ω) P := by
  set L : ℝ × (ι → ℝ) →L[ℝ] (Unit → ℝ) × (ι → ℝ) :=
    (ContinuousLinearMap.pi fun _ : Unit => ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)) with hL
  have h1 : HasGaussianLaw (fun ω => (fun _ : Unit => U ω, fun j => W j ω)) P := by
    have := hUW.map_fun L
    simpa [hL] using this
  have h2 := h1.indepFun_of_covariance_eval (X := fun _ : Unit => U) (fun _ j => hcov j)
  exact h2.comp (measurable_pi_apply ()) measurable_id

/-- **Gaussian integration by parts** (multivariate Stein identity): for a jointly Gaussian
`(U, V₁, …, V_n)` with `𝔼 U = 0` and `G : ℝⁿ → ℝ` bounded with bounded continuous partial
derivatives `G' j = ∂ⱼG`,
`𝔼[U G(V)] = ∑ⱼ Cov(U, Vⱼ) 𝔼[∂ⱼG(V)]`.
Source: Vershynin 2018, Lemma 7.2.3; Talagrand, *Mean Field Models for Spin Glasses*, Lemma
1.3.1. Proof: regress `V` on `U` (`V = c U + W` with `W ⫫ U`), apply the one-dimensional
identity in `U` and integrate over `W`. Atlas: `gaussian-integration-by-parts`. Ported from
Prove2me solution `GaussianMatrix.gaussian_integration_by_parts`. -/
theorem integral_mul_eq_sum_covariance_mul_integral {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {P : Measure Ω} (U : Ω → ℝ) (V : ι → Ω → ℝ)
    (hUV : HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P) (hU0 : ∫ ω, U ω ∂P = 0)
    (G : (ι → ℝ) → ℝ) (G' : ι → (ι → ℝ) → ℝ)
    (hG : ∀ x, HasFDerivAt G
      (∑ j, G' j x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x)
    (hG'c : ∀ j, Continuous (G' j)) (C : ℝ) (hGb : ∀ x, |G x| ≤ C)
    (hG'b : ∀ j x, |G' j x| ≤ C) :
    ∫ ω, U ω * G (fun j => V j ω) ∂P = ∑ j, cov[U, V j; P] * ∫ ω, G' j (fun j => V j ω) ∂P := by
  have hP := hUV.isProbabilityMeasure
  have hUm : MemLp U 2 P := hUV.fst.memLp_two
  have hVm : ∀ j, MemLp (V j) 2 P := fun j => (hUV.snd.eval j).memLp_two
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  have hUae : AEMeasurable U P := hUV.fst.aemeasurable
  have hVae : AEMeasurable (fun ω j => V j ω) P := hUV.snd.aemeasurable
  set σ2 := Var[U; P] with hσ2
  by_cases hσ : σ2 = 0
  · have hU : ∀ᵐ ω ∂P, U ω = 0 := by
      filter_upwards [ae_eq_integral_of_variance_eq_zero hUm hσ] with ω hω
      rw [hω, hU0]
    have hL : ∫ ω, U ω * G (fun j => V j ω) ∂P = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards [hU] with ω hω; simp [hω]
    have hc : ∀ j, cov[U, V j; P] = 0 := by
      intro j
      rw [covariance, integral_eq_zero_of_ae]
      filter_upwards [hU] with ω hω; simp [hω, hU0]
    simp [hL, hc]
  have hσpos : 0 < σ2 := lt_of_le_of_ne (variance_nonneg U P) (Ne.symm hσ)
  set c : ι → ℝ := fun j => cov[U, V j; P] / σ2 with hc
  set W : ι → Ω → ℝ := fun j ω => V j ω - U ω * c j with hW
  -- joint law of (U, W)
  set L : ℝ × (ι → ℝ) →L[ℝ] ℝ × (ι → ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ) - (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).smulRight c)
    with hLdef
  have hUW : HasGaussianLaw (fun ω => (U ω, fun j => W j ω)) P := by
    have := hUV.map_fun L
    have heq : (fun ω => (U ω, fun j => W j ω)) = fun ω => L (U ω, fun j => V j ω) := by
      funext ω
      simp only [hLdef, hW]
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
        sub_apply, ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.smulRight_apply]
      ext j <;> simp
    rw [heq]; exact this
  have hcovW : ∀ j, cov[U, W j; P] = 0 := by
    intro j
    rw [hW]
    simp only
    rw [covariance_fun_sub_right hUm (hVm j) (hUm.mul_const _), covariance_mul_const_right,
      covariance_self hUae, ← hσ2, hc]
    field_simp
    ring
  have hind := indepFun_of_hasGaussianLaw_of_covariance_eq_zero U W hUW hcovW
  set Wv : Ω → (ι → ℝ) := fun ω j => W j ω with hWv
  have hWae : AEMeasurable Wv P := hUW.snd.aemeasurable
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hUae hWae).1 hind
  have hmapU : P.map U = gaussianReal 0 σ2.toNNReal := by
    rw [hUV.fst.map_eq_gaussianReal, hU0]
  have hVeq : ∀ ω, (fun j => V j ω) = U ω • c + Wv ω := by
    intro ω; ext j; simp [hWv, hW]
  -- generic transfer
  have hpm : AEMeasurable (fun ω => (U ω, Wv ω)) P := hUae.prodMk hWae
  have htrans : ∀ F : ℝ × (ι → ℝ) → ℝ, Continuous F →
      Integrable (fun ω => F (U ω, Wv ω)) P →
      ∫ ω, F (U ω, Wv ω) ∂P = ∫ w, ∫ u, F (u, w) ∂(P.map U) ∂(P.map Wv) := by
    intro F hF hFi
    have h1 : ∫ ω, F (U ω, Wv ω) ∂P = ∫ p, F p ∂(P.map (fun ω => (U ω, Wv ω))) :=
      (integral_map hpm hF.aestronglyMeasurable).symm
    have hint : Integrable F (P.map (fun ω => (U ω, Wv ω))) :=
      (integrable_map_measure hF.aestronglyMeasurable hpm).2 hFi
    rw [h1, hprod]
    rw [hprod] at hint
    exact integral_prod_symm F hint
  set F1 : ℝ × (ι → ℝ) → ℝ := fun p => p.1 * G (p.1 • c + p.2) with hF1
  set F2 : ℝ × (ι → ℝ) → ℝ := fun p => ∑ j, G' j (p.1 • c + p.2) * c j with hF2
  have hF1c : Continuous F1 := by rw [hF1]; fun_prop
  have hF2c : Continuous F2 := by
    rw [hF2]
    exact continuous_finsetSum _ fun j _ => ((hG'c j).comp (by fun_prop)).mul continuous_const
  set K := C * ∑ j, |c j| with hK
  have hF2b : ∀ p, |F2 p| ≤ K := by
    intro p
    rw [hF2, hK, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hG'b j _) (abs_nonneg _)
  have hF1i : Integrable (fun ω => F1 (U ω, Wv ω)) P := by
    refine Integrable.mono' ((hUm.integrable one_le_two).norm.const_mul C)
      (hF1c.comp_aestronglyMeasurable hpm.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    simp only [hF1, Real.norm_eq_abs, abs_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hGb _) (abs_nonneg _)
  have hF2i : Integrable (fun ω => F2 (U ω, Wv ω)) P := by
    refine Integrable.mono' (integrable_const K)
      (hF2c.comp_aestronglyMeasurable hpm.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]; exact hF2b _
  have hσnn : ((σ2.toNNReal : NNReal) : ℝ) = σ2 := Real.coe_toNNReal _ hσpos.le
  have hinner : ∀ w : ι → ℝ, ∫ u, F1 (u, w) ∂(P.map U) = σ2 * ∫ u, F2 (u, w) ∂(P.map U) := by
    intro w
    rw [hmapU]
    have := integral_mul_eq_mul_integral_deriv_gaussianReal σ2.toNNReal (fun u => G (u • c + w))
      (fun u => F2 (u, w)) ?_
      (hF2c.comp (by fun_prop)) C K (fun u => hGb _) (fun u => hF2b _)
    · rw [hσnn] at this
      simpa [hF1] using this
    · intro u
      have hd : HasDerivAt (fun u : ℝ => u • c + w) ((1 : ℝ) • c) u :=
        ((hasDerivAt_id u).smul_const c).add_const w
      have := (hG (u • c + w)).comp_hasDerivAt u hd
      have e : F2 (u, w) = (∑ j, G' j (u • c + w) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) ((1 : ℝ) • c) := by
        simp [hF2]
      rw [e]; exact this
  have hLHS : ∫ ω, U ω * G (fun j => V j ω) ∂P = ∫ ω, F1 (U ω, Wv ω) ∂P := by
    congr 1; ext ω; rw [hVeq ω]
  rw [hLHS, htrans F1 hF1c hF1i]
  simp_rw [hinner]
  rw [integral_const_mul, ← htrans F2 hF2c hF2i]
  simp only [hF2, ← hVeq]
  rw [integral_finsetSum _ (fun j _ => ?_), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const, hc]
    field_simp
  · refine Integrable.mono' (integrable_const (C * |c j|))
      ((((hG'c j).comp_aestronglyMeasurable hVae.aestronglyMeasurable)).mul_const _)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hG'b j _) (abs_nonneg _)

end NLAlib
