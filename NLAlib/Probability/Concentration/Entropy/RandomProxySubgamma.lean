import NLAlib.Probability.Concentration.Entropy.WeightedProxyEntropy
import NLAlib.Probability.Concentration.Entropy.SelfBoundingMGF
import NLAlib.Probability.Concentration.Entropy.TwoSidedProxyEntropy

/-!
# Two-sided subgamma moments from an actual random variance proxy

The product-law replacement entropy is derived rather than assumed. Gibbs
duality uses the actual exponential integral of the proxy, and native MGF
derivatives integrate the resulting rational entropy estimate. The proxy's
exponential-integral estimate is an intermediate input, supplied separately
by the checked deletion theorem. This module does not claim the sharper
literal constants of source equation (5.1).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace NLAlib

private theorem randomProxy_entropy_factor_le
    {a E u : ℝ} (ha : 0 < a) (hE : 0 ≤ E) (hu : 0 ≤ u)
    (hdom : Real.sqrt (6 * a) * u < 1) :
    (3 * u ^ 2) / ((2 * a)⁻¹ - 3 * u ^ 2) * (E / a) ≤
      (6 * E) * u ^ 2 / (1 - Real.sqrt (6 * a) * u) ^ 2 := by
  have hc : 0 ≤ Real.sqrt (6 * a) := Real.sqrt_nonneg _
  have hcsq : Real.sqrt (6 * a) ^ 2 = 6 * a := Real.sq_sqrt (by positivity)
  have hcu : 0 ≤ Real.sqrt (6 * a) * u := mul_nonneg hc hu
  have hcusq : (Real.sqrt (6 * a) * u) ^ 2 < 1 :=
    by simpa only [one_pow] using
      (sq_lt_sq₀ hcu (by norm_num : (0 : ℝ) ≤ 1)).mpr hdom
  have hden : 0 < 1 - 6 * a * u ^ 2 := by
    rw [mul_pow, hcsq] at hcusq
    linarith
  have hθ : 0 < (2 * a)⁻¹ - 3 * u ^ 2 := by
    apply sub_pos.mpr
    rw [← one_div]
    apply (lt_div_iff₀ (by positivity : 0 < 2 * a)).mpr
    nlinarith
  have he : (3 * u ^ 2) / ((2 * a)⁻¹ - 3 * u ^ 2) * (E / a) =
      (6 * E) * u ^ 2 / (1 - 6 * a * u ^ 2) := by
    field_simp [ha.ne', hθ.ne', hden.ne']
    ring
  rw [he]
  apply (div_le_div_iff₀ hden (sq_pos_of_pos (sub_pos.mpr hdom))).mpr
  have hsq : (1 - Real.sqrt (6 * a) * u) ^ 2 ≤ 1 - 6 * a * u ^ 2 := by
    nlinarith [mul_nonneg hcu (sub_nonneg.mpr hdom.le)]
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-- Actual centered exponential moments in either sign, with a common random
proxy on the original/copy product law. The assumptions concern boundedness,
coordinate replacement differences, a computed positive-gradient upper bound,
and the proxy's actual finite exponential integral. Gibbs and Herbst are proved
inside the argument; no desired entropy or centered-MGF conclusion is assumed.

The case `a>0` is deliberate. A generic zero self-bounding coefficient permits
nonzero constant proxies and is not identified with a zero random variable. -/
theorem integral_exp_sign_mul_sub_integral_pi_le_of_random_proxy
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (f : (ι → Ω) → ℝ) (hfm : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M)
    (W : ((ι → Ω) × (ι → Ω)) → ℝ)
    (hWi : Integrable W ((Measure.pi ν).prod (Measure.pi ν)))
    (hgrad : ∀ᵐ q ∂((Measure.pi ν).prod (Measure.pi ν)),
      (∑ i, max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2) ≤ W q)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b ^ 2 ≤ a)
    (hdiff : ∀ i, ∀ᵐ q ∂((Measure.pi ν).prod (Measure.pi ν)),
      |f q.1 - f (Function.update q.1 i (q.2 i))| ≤ b)
    (hWexp : Integrable (fun q => Real.exp (W q / (2 * a)))
      ((Measure.pi ν).prod (Measure.pi ν)))
    (hWlog : Real.log (∫ q, Real.exp (W q / (2 * a))
      ∂((Measure.pi ν).prod (Measure.pi ν))) ≤
        (∫ q, W q ∂((Measure.pi ν).prod (Measure.pi ν))) / a)
    {s : ℝ} (hs : 0 ≤ s) (hdom : Real.sqrt (6 * a) * s < 1)
    {e : ℝ} (he : e = 1 ∨ e = -1) :
    (∫ x, Real.exp (s * (e * (f x - ∫ y, f y ∂Measure.pi ν))) ∂Measure.pi ν) ≤
      Real.exp ((6 * ∫ q, W q ∂((Measure.pi ν).prod (Measure.pi ν))) *
        s ^ 2 / (1 - Real.sqrt (6 * a) * s)) := by
  let μ := Measure.pi ν
  let P := μ.prod μ
  let g : (ι → Ω) → ℝ := fun x => e * f x
  have hgm : Measurable g := by fun_prop
  have hgb : ∀ x, |g x| ≤ M := by
    intro x
    rcases he with rfl | rfl
    · simpa only [g, one_mul] using hbound x
    · simpa only [g, neg_one_mul, abs_neg] using hbound x
  have hW0 : ∀ᵐ q ∂P, 0 ≤ W q :=
    hgrad.mono fun q hq => (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans hq
  have hEW : 0 ≤ ∫ q, W q ∂P := integral_nonneg_of_ae hW0
  have hint (u : ℝ) : Integrable (fun x => Real.exp (u * g x)) μ :=
    integrable_exp_mul_of_mem_Icc hgm.aemeasurable
      (ae_of_all _ fun x => abs_le.mp (hgb x))
  have hc : 0 ≤ Real.sqrt (6 * a) := Real.sqrt_nonneg _
  have hbc : b ≤ Real.sqrt (6 * a) := by
    apply (sq_le_sq₀ hb hc).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith
  have hent (u : ℝ) (hu : 0 < u) (hcu : Real.sqrt (6 * a) * u < 1) :
      (∫ x, u * g x * Real.exp (u * g x) ∂μ) -
        (∫ x, Real.exp (u * g x) ∂μ) * Real.log (∫ x, Real.exp (u * g x) ∂μ) ≤
      ((6 * ∫ q, W q ∂P) * u ^ 2 / (1 - Real.sqrt (6 * a) * u) ^ 2) *
        ∫ x, Real.exp (u * g x) ∂μ := by
    let Y : ((ι → Ω) × (ι → Ω)) → ℝ := fun q => Real.exp (u * g q.1)
    have hYi : Integrable Y P := (hint u).comp_fst μ
    have hYlogb : Integrable (fun x =>
        Real.exp (u * g x) * Real.log (Real.exp (u * g x))) μ := by
      have h := ((hint u).bdd_mul hgm.aestronglyMeasurable
        (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hgb x)).const_mul u
      convert h using 1
      ext x
      rw [Real.log_exp]
      ring
    have hYlog : Integrable (fun q => Y q * Real.log (Y q)) P := hYlogb.comp_fst μ
    have hYint : (∫ q, Y q ∂P) = ∫ x, Real.exp (u * g x) ∂μ := by
      simpa only [probReal_univ, one_smul] using
        (integral_fun_fst (μ := μ) (ν := μ) (fun x => Real.exp (u * g x)))
    have hYlogint : (∫ q, Y q * Real.log (Y q) ∂P) =
        ∫ x, Real.exp (u * g x) * Real.log (Real.exp (u * g x)) ∂μ := by
      simpa only [probReal_univ, one_smul] using
        (integral_fun_fst (μ := μ) (ν := μ) (fun x => Real.exp (u * g x) *
          Real.log (Real.exp (u * g x))))
    have hYV : Integrable (fun q => Y q * W q) P := by
      apply hWi.bdd_mul (by fun_prop) (c := Real.exp (|u| * M))
      exact ae_of_all _ fun q => by
        simpa only [Y, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
          Real.exp_mul_le_exp_abs_mul_of_abs_le (s := u) (hgb q.1)
    have hVi : Integrable (fun q => Real.exp ((2 * a)⁻¹ * W q)) P := by
      convert hWexp using 1
      ext q
      congr 1
      ring
    have hub : u * b ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hbc hu.le]
    have hp := entropy_exp_sign_mul_pi_le_three_integral_proxy_of_bounded
      ν f hfm M hM hbound W hWi hgrad hdiff hu.le hub he
    have hproxy : (∫ q, Y q * Real.log (Y q) ∂P) -
        (∫ q, Y q ∂P) * Real.log (∫ q, Y q ∂P) ≤
      (3 * u ^ 2) * ∫ q, Y q * W q ∂P := by
      rw [hYint, hYlogint]
      simpa only [Y, g, P, μ, Real.log_exp, mul_comm, mul_left_comm, mul_assoc] using hp
    have hcsq : Real.sqrt (6 * a) ^ 2 = 6 * a := Real.sq_sqrt (by positivity)
    have hcusq : (Real.sqrt (6 * a) * u) ^ 2 < 1 :=
      by simpa only [one_pow] using
        (sq_lt_sq₀ (mul_nonneg hc hu.le) (by norm_num : (0 : ℝ) ≤ 1)).mpr hcu
    have hθ : 3 * u ^ 2 < (2 * a)⁻¹ := by
      rw [mul_pow, hcsq] at hcusq
      rw [← one_div]
      apply (lt_div_iff₀ (by positivity : 0 < 2 * a)).mpr
      nlinarith
    have hG := entropy_le_mul_log_integral_exp_of_weighted_proxy
      P Y W (fun q => Real.exp_pos _) hYi hYlog hYV
      (by positivity : 0 ≤ 3 * u ^ 2) hθ hVi hproxy
    have hlog : Real.log (∫ q, Real.exp ((2 * a)⁻¹ * W q) ∂P) ≤
        (∫ q, W q ∂P) / a := by
      have hfun : (fun q => Real.exp ((2 * a)⁻¹ * W q)) =
          (fun q => Real.exp (W q / (2 * a))) := by
        ext q
        congr 1
        ring
      rw [hfun]
      exact hWlog
    have hEY : 0 ≤ ∫ q, Y q ∂P := integral_nonneg fun _ => (Real.exp_pos _).le
    have hG' := hG.trans (mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (div_nonneg (by positivity) (sub_pos.mpr hθ).le) hEY))
    have hf := randomProxy_entropy_factor_le ha hEW hu.le hcu
    have hf' := mul_le_mul_of_nonneg_right hf hEY
    have hall := hG'.trans (by
      calc (3 * u ^ 2) / ((2 * a)⁻¹ - 3 * u ^ 2) * (∫ q, Y q ∂P) *
          ((∫ q, W q ∂P) / a) =
          ((3 * u ^ 2) / ((2 * a)⁻¹ - 3 * u ^ 2) * ((∫ q, W q ∂P) / a)) *
            (∫ q, Y q ∂P) := by ring
        _ ≤ _ := hf')
    rw [hYint, hYlogint] at hall
    simpa only [Y, P, Real.log_exp, mul_comm, mul_left_comm, mul_assoc] using hall
  have h := integral_exp_mul_le_exp_of_rational_entropy_le μ g hc hint hent hs hdom
  have hmean : (∫ x, g x ∂μ) = e * ∫ x, f x ∂μ := by
    dsimp [g]
    rw [integral_const_mul]
  rw [hmean] at h
  have hfun : (fun x => Real.exp (s * (e * (f x - ∫ y, f y ∂μ)))) =
      (fun x => Real.exp (-(s * (e * ∫ y, f y ∂μ))) * Real.exp (s * g x)) := by
    ext x
    rw [← Real.exp_add]
    congr 1
    dsimp [g]
    ring
  rw [hfun, integral_const_mul]
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(s * (e * ∫ y, f y ∂μ)))).le
  exact hmul.trans_eq (by rw [← Real.exp_add]; congr 1; ring)

end NLAlib
