import NLAlib.Gaussian.Concentration.LogSobolev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Gaussian logarithmic Sobolev inequality without an entropy-integrability hypothesis

Atlas: `gaussian-log-sobolev`. Smooth bounded value truncations
`c sin(f/c)` have derivative `cos(f/c) df`, so their Dirichlet energies
never exceed that of `f`. Applying the existing LSI to these bounded
functions and then Fatou to `f² log(f²) + 1` proves entropy integrability.
The existing constant-two inequality then applies to `f` itself.

Source: Gross 1975, Thm. 5; Ledoux, Thm. 5.1. The local registry's
`PP-07/T-0002` is downstream of LSI and is not used to prove LSI.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace NLAlib

/-- A smooth bounded value truncation. Source: the elementary sine/sinc
identities in Mathlib. Atlas: `gaussian-log-sobolev` (approximation helper).
atlas: gaussian-log-sobolev -/
def sineTruncation (c y : ℝ) : ℝ := c * Real.sin (c⁻¹ * y)

/-- The sine truncation is a sinc multiplier, including at zero. Source:
Mathlib's `Real.sinc_of_ne_zero`. Atlas: `gaussian-log-sobolev`. -/
theorem sineTruncation_eq_mul_sinc {c : ℝ} (hc : c ≠ 0) (y : ℝ) :
    sineTruncation c y = y * Real.sinc (c⁻¹ * y) := by
  by_cases hy : y = 0
  · simp [sineTruncation, hy]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero (inv_ne_zero hc) hy), sineTruncation]
    field_simp

/-- Smooth sine truncation does not increase absolute value. Source:
Mathlib's `Real.abs_sinc_le_one`. Atlas: `gaussian-log-sobolev`. -/
theorem abs_sineTruncation_le {c : ℝ} (hc : c ≠ 0) (y : ℝ) :
    |sineTruncation c y| ≤ |y| := by
  rw [sineTruncation_eq_mul_sinc hc, abs_mul]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (abs_nonneg y)).trans_eq
    (mul_one _)

/-- Sine truncation is bounded by its positive scale. Source: Mathlib's
`Real.abs_sin_le_one`. Atlas: `gaussian-log-sobolev`. -/
theorem abs_sineTruncation_le_scale {c : ℝ} (hc : 0 < c) (y : ℝ) :
    |sineTruncation c y| ≤ c := by
  rw [sineTruncation, abs_mul, abs_of_pos hc]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hc.le).trans_eq (mul_one _)

/-- Sine truncation preserves C1 smoothness. Source: Mathlib's
`ContDiff.sin`. Atlas: `gaussian-log-sobolev`. -/
theorem contDiff_sineTruncation_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 1 f) (c : ℝ) :
    ContDiff ℝ 1 (fun x => sineTruncation c (f x)) := by
  change ContDiff ℝ 1 (fun x => c * Real.sin (c⁻¹ * f x))
  exact contDiff_const.mul ((contDiff_const.mul hf).sin)

/-- The derivative multiplier of the smooth truncation has absolute value
at most one. Source: Mathlib's `HasFDerivAt.sin`.
Atlas: `gaussian-log-sobolev`. -/
theorem fderiv_sineTruncation_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    {c : ℝ} (hc : c ≠ 0) :
    fderiv ℝ (fun x => sineTruncation c (f x)) x =
      Real.cos (c⁻¹ * f x) • fderiv ℝ f x := by
  have h := (((hf.hasFDerivAt.const_mul c⁻¹).sin).const_mul c).fderiv
  have he : c * (Real.cos (c⁻¹ * f x) * c⁻¹) = Real.cos (c⁻¹ * f x) := by
    field_simp
  simpa only [sineTruncation, smul_smul, he] using h

/-- Smooth bounded sine truncations converge pointwise to the original
value as the scales tend to infinity. Source: continuity of `Real.sinc`
at zero. Atlas: `gaussian-log-sobolev`. -/
theorem tendsto_sineTruncation_nat (y : ℝ) :
    Tendsto (fun n : ℕ => sineTruncation ((n : ℝ) + 1) y) atTop (nhds y) := by
  have hscale : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * y) atTop (nhds 0) := by
    simpa only [one_div, zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const y
  have hsinc := (Real.continuous_sinc.tendsto (0 : ℝ)).comp hscale
  have h := (tendsto_const_nhds (x := y)).mul hsinc
  have he (n : ℕ) : sineTruncation ((n : ℝ) + 1) y =
      y * Real.sinc (((n : ℝ) + 1)⁻¹ * y) :=
    sineTruncation_eq_mul_sinc (by positivity) y
  simpa only [Function.comp_def, Real.sinc_zero, mul_one, ← he] using h

/-- A logarithmic Sobolev bound already proved for C1 functions with finite
entropy entails entropy integrability for every C1 function with finite
square and gradient energy. This closure lemma assumes the displayed LSI
as an explicit premise; the Gaussian corollaries below discharge it with
the existing proved Gaussian inequalities. Source: bounded smooth
truncation and Fatou's lemma. Atlas: `gaussian-log-sobolev`. -/
theorem integrable_sq_mul_log_sq_of_logSobolev_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    {ι : Type*} [Fintype ι] (v : ι → E) (C : ℝ) (hC : 0 ≤ C)
    (hLSI : ∀ h : E → ℝ, ContDiff ℝ 1 h →
      Integrable (fun x => h x ^ 2) ν →
      Integrable (fun x => h x ^ 2 * Real.log (h x ^ 2)) ν →
      Integrable (fun x => ∑ i, fderiv ℝ h x (v i) ^ 2) ν →
      (∫ x, h x ^ 2 * Real.log (h x ^ 2) ∂ν) -
        (∫ x, h x ^ 2 ∂ν) * Real.log (∫ x, h x ^ 2 ∂ν) ≤
          C * ∫ x, ∑ i, fderiv ℝ h x (v i) ^ 2 ∂ν)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (hf2 : Integrable (fun x => f x ^ 2) ν)
    (hdf : Integrable (fun x => ∑ i, fderiv ℝ f x (v i) ^ 2) ν) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) ν := by
  let c : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  let fN : ℕ → E → ℝ := fun n x => sineTruncation (c n) (f x)
  have hNcd (n : ℕ) : ContDiff ℝ 1 (fN n) := contDiff_sineTruncation_comp hf (c n)
  have hNabs (n : ℕ) (x : E) : |fN n x| ≤ |f x| := abs_sineTruncation_le (hc n).ne' _
  have hNsq (n : ℕ) (x : E) : fN n x ^ 2 ≤ f x ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hNabs n x) 2
  have hN2 (n : ℕ) : Integrable (fun x => fN n x ^ 2) ν := by
    refine hf2.mono' ((hNcd n).continuous.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hNsq n x
  have hNlog (n : ℕ) : Integrable (fun x => fN n x ^ 2 * Real.log (fN n x ^ 2)) ν := by
    refine Integrable.mono' (integrable_const (c n ^ 4 + 1))
      (Real.continuous_mul_log.comp ((hNcd n).continuous.pow 2)).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    have habs := abs_sineTruncation_le_scale (hc n) (f x)
    have hsq : fN n x ^ 2 ≤ c n ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
    have h4 : (fN n x ^ 2) ^ 2 ≤ c n ^ 4 := by nlinarith [sq_nonneg (fN n x)]
    exact (abs_mul_log_le_sq_add_one (fN n x ^ 2) (sq_nonneg _)).trans (by linarith)
  have hNdf_eq (n : ℕ) (x : E) (i : ι) :
      fderiv ℝ (fN n) x (v i) = Real.cos ((c n)⁻¹ * f x) * fderiv ℝ f x (v i) := by
    rw [fderiv_sineTruncation_comp (hf.differentiable (by norm_num)).differentiableAt (hc n).ne']
    rfl
  have hNdf_le (n : ℕ) (x : E) :
      ∑ i, fderiv ℝ (fN n) x (v i) ^ 2 ≤ ∑ i, fderiv ℝ f x (v i) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [hNdf_eq, mul_pow]
    have hcos : Real.cos ((c n)⁻¹ * f x) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq ((c n)⁻¹ * f x), sq_nonneg (Real.sin ((c n)⁻¹ * f x))]
    nlinarith [sq_nonneg (fderiv ℝ f x (v i))]
  have hNdf (n : ℕ) : Integrable (fun x => ∑ i, fderiv ℝ (fN n) x (v i) ^ 2) ν := by
    have hm : Continuous (fun x => ∑ i, fderiv ℝ (fN n) x (v i) ^ 2) := by
      exact continuous_finsetSum _ fun i _ =>
        (((hNcd n).continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2
    refine hdf.mono' hm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact hNdf_le n x
  let M := ∫ x, f x ^ 2 ∂ν
  let G := ∫ x, ∑ i, fderiv ℝ f x (v i) ^ 2 ∂ν
  let B := C * G + M ^ 2 + 2
  have hM : 0 ≤ M := integral_nonneg fun x => sq_nonneg _
  have hNmean (n : ℕ) : (∫ x, fN n x ^ 2 ∂ν) ≤ M := integral_mono (hN2 n) hf2 (hNsq n)
  have hNenergy (n : ℕ) : (∫ x, ∑ i, fderiv ℝ (fN n) x (v i) ^ 2 ∂ν) ≤ G :=
    integral_mono (hNdf n) hdf (hNdf_le n)
  let F : E → ℝ := fun x => f x ^ 2 * Real.log (f x ^ 2) + 1
  let FN : ℕ → E → ℝ := fun n x => fN n x ^ 2 * Real.log (fN n x ^ 2) + 1
  have hF0 (x : E) : 0 ≤ F x := by
    have h := Real.self_sub_one_le_mul_log (sq_nonneg (f x))
    dsimp [F]
    nlinarith [sq_nonneg (f x)]
  have hFN0 (n : ℕ) (x : E) : 0 ≤ FN n x := by
    have h := Real.self_sub_one_le_mul_log (sq_nonneg (fN n x))
    dsimp [FN]
    nlinarith [sq_nonneg (fN n x)]
  have hFNm (n : ℕ) : Measurable (FN n) :=
    ((Real.continuous_mul_log.comp ((hNcd n).continuous.pow 2)).add continuous_const).measurable
  have hFNi (n : ℕ) : Integrable (FN n) ν := (hNlog n).add (integrable_const _)
  have hFNbound (n : ℕ) : (∫ x, FN n x ∂ν) ≤ B := by
    have hlsi := hLSI (fN n) (hNcd n) (hN2 n) (hNlog n) (hNdf n)
    have hm0 : 0 ≤ ∫ x, fN n x ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have hmLog := abs_mul_log_le_sq_add_one (∫ x, fN n x ^ 2 ∂ν) hm0
    have hmSq := pow_le_pow_left₀ hm0 (hNmean n) 2
    have he := mul_le_mul_of_nonneg_left (hNenergy n) hC
    have ha := le_abs_self ((∫ x, fN n x ^ 2 ∂ν) * Real.log (∫ x, fN n x ^ 2 ∂ν))
    change (∫ x, fN n x ^ 2 * Real.log (fN n x ^ 2) + 1 ∂ν) ≤ B
    have hOne : (∫ _x : E, (1 : ℝ) ∂ν) = 1 := by simp
    rw [integral_add (hNlog n) (integrable_const _)]
    rw [hOne]
    dsimp [B]
    linarith
  have hFNlim (x : E) : Tendsto (fun n => ENNReal.ofReal (FN n x)) atTop
      (nhds (ENNReal.ofReal (F x))) := by
    have hlim : Tendsto (fun n => fN n x) atTop (nhds (f x)) := tendsto_sineTruncation_nat (f x)
    have hloglim := (Real.continuous_mul_log.tendsto (f x ^ 2)).comp (hlim.pow 2)
    exact (ENNReal.continuous_ofReal.tendsto _).comp (hloglim.add tendsto_const_nhds)
  have hFatou : (∫⁻ x, ENNReal.ofReal (F x) ∂ν) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (FN n x) ∂ν) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (FN n x)) atTop ∂ν :=
        lintegral_congr_ae (ae_of_all _ fun x => (hFNlim x).liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp (hFNm n)
  have hLinbound (n : ℕ) : (∫⁻ x, ENNReal.ofReal (FN n x) ∂ν) ≤ ENNReal.ofReal B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFNi n) (ae_of_all _ (hFN0 n))]
    exact ENNReal.ofReal_le_ofReal (hFNbound n)
  have hLiminf : liminf (fun n => ∫⁻ x, ENNReal.ofReal (FN n x) ∂ν) atTop ≤ ENNReal.ofReal B := by
    have h : liminf (fun n => ∫⁻ x, ENNReal.ofReal (FN n x) ∂ν) atTop ≤
        liminf (fun _n : ℕ => ENNReal.ofReal B) atTop :=
      liminf_le_liminf (Eventually.of_forall hLinbound)
    simpa using h
  have hFin : (∫⁻ x, ENNReal.ofReal (F x) ∂ν) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hFatou.trans hLiminf)
  have hFm : AEStronglyMeasurable F ν :=
    ((Real.continuous_mul_log.comp (hf.continuous.pow 2)).add continuous_const).aestronglyMeasurable
  have hFi := (lintegral_ofReal_ne_top_iff_integrable hFm (ae_of_all _ hF0)).1 hFin
  have h := hFi.sub (integrable_const (1 : ℝ))
  refine h.congr (ae_of_all _ fun x => ?_)
  change (f x ^ 2 * Real.log (f x ^ 2) + 1) - 1 = f x ^ 2 * Real.log (f x ^ 2)
  ring

/-- Square and gradient-energy integrability imply entropy integrability
under the whole finite product standard Gaussian law. Source: Gross 1975,
Thm. 5, via the bounded-test closure proved above.
Atlas: `gaussian-log-sobolev`.
atlas: gaussian-log-sobolev -/
theorem integrable_sq_mul_log_sq_gaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hf2 : Integrable (fun x => f x ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hdf : Integrable (fun x => ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  apply integrable_sq_mul_log_sq_of_logSobolev_bound (fun i : ι => Pi.single i 1) 2 (by norm_num)
    (fun h hcd h2 hlog hd => entropy_sq_le_two_mul_integral_sum_sq_fderiv_gaussian h hcd h2 hlog hd)
    f hf hf2 hdf

/-- Gaussian logarithmic Sobolev inequality with the intended square and
gradient-energy assumptions only; entropy integrability is proved rather
than assumed. Source: Gross 1975, Thm. 5; Ledoux, Thm. 5.1.
Atlas: `gaussian-log-sobolev`. Constant `2`, including empty dimensions.
atlas: gaussian-log-sobolev -/
theorem entropy_sq_le_two_mul_integral_sum_sq_fderiv_gaussian_of_integrable
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hf2 : Integrable (fun x => f x ^ 2) (Measure.pi fun _ : ι => gaussianReal 0 1))
    (hdf : Integrable (fun x => ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
      (Measure.pi fun _ : ι => gaussianReal 0 1)) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      - (∫ x, f x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) *
        Real.log (∫ x, f x ^ 2 ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤
      2 * ∫ x, ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) :=
  entropy_sq_le_two_mul_integral_sum_sq_fderiv_gaussian f hf hf2
    (integrable_sq_mul_log_sq_gaussian f hf hf2 hdf) hdf

/-- In dimension one, square and derivative-square integrability suffice
for entropy integrability. Source: Gross 1975, Thm. 5; Ledoux, Thm. 5.1.
Atlas: `gaussian-log-sobolev`. -/
theorem integrable_sq_mul_log_sq_gaussianReal (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hf2 : Integrable (fun x => f x ^ 2) (gaussianReal 0 1))
    (hdf : Integrable (fun x => deriv f x ^ 2) (gaussianReal 0 1)) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (gaussianReal 0 1) := by
  apply integrable_sq_mul_log_sq_of_logSobolev_bound (fun _ : Unit => (1 : ℝ)) 2 (by norm_num)
    ?_ f hf hf2 ?_
  · intro h hcd h2 hlog hd
    have hd' : Integrable (fun x => deriv h x ^ 2) (gaussianReal 0 1) := by
      simpa only [Fintype.sum_unique, fderiv_apply_one_eq_deriv] using hd
    simpa only [Fintype.sum_unique, fderiv_apply_one_eq_deriv] using
      entropy_sq_le_two_mul_integral_sq_deriv_gaussianReal h hcd h2 hlog hd'
  · simpa only [Fintype.sum_unique, fderiv_apply_one_eq_deriv] using hdf

/-- One-dimensional Gaussian LSI with no entropy-integrability premise.
Source: Gross 1975, Thm. 5; Ledoux, Thm. 5.1.
Atlas: `gaussian-log-sobolev`. Constant `2`.
atlas: gaussian-log-sobolev -/
theorem entropy_sq_le_two_mul_integral_sq_deriv_gaussianReal_of_integrable
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hf2 : Integrable (fun x => f x ^ 2) (gaussianReal 0 1))
    (hdf : Integrable (fun x => deriv f x ^ 2) (gaussianReal 0 1)) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂(gaussianReal 0 1)
      - (∫ x, f x ^ 2 ∂(gaussianReal 0 1)) * Real.log (∫ x, f x ^ 2 ∂(gaussianReal 0 1)) ≤
        2 * ∫ x, deriv f x ^ 2 ∂(gaussianReal 0 1) :=
  entropy_sq_le_two_mul_integral_sq_deriv_gaussianReal f hf hf2
    (integrable_sq_mul_log_sq_gaussianReal f hf hf2 hdf) hdf

end NLAlib
