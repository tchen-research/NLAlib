import NLAlib.ForMathlib.MeasureTheory.TailOrder
import NLAlib.Probability.SubGaussian.OrliczMGF
import NLAlib.Probability.Gaussian.Moments.PositiveMoments
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Scalar Gaussian domination from an exponential square moment

The independent-copy argument, scalar upper-tail comparison, and convex
contraction used in the finite-series comparison. Source: the finite scalar
reroute in `random_matrices_probability_concentration_reroutes_2026_10_16.tex`,
Lemma “Scalar domination, followed by finite contraction”.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLAlib

/-- A unit interval to the right of `x` provides a lower Gaussian absolute tail.
The coarse denominator three avoids special-function tail estimates. -/
theorem ofReal_exp_neg_sq_le_gaussianReal_abs_gt {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal ((1 / 3 : ℝ) * Real.exp (-(x + 1) ^ 2 / 2)) ≤
      gaussianReal 0 1 {g : ℝ | x < |g|} := by
  have hs : Real.sqrt (2 * Real.pi) ≤ 3 := by
    have h := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
    have hn := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith [Real.pi_lt_four]
  have hi : (1 / 3 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)) hs
  have hpdf : ∀ u ∈ Ioc x (x + 1),
      (1 / 3 : ℝ) * Real.exp (-(x + 1) ^ 2 / 2) ≤ gaussianPDFReal 0 1 u := by
    intro u hu
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have he : Real.exp (-(x + 1) ^ 2 / 2) ≤ Real.exp (-u ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hu.1, hu.2]
    exact mul_le_mul hi he (Real.exp_pos _).le (by positivity)
  calc
    _ = ∫⁻ _ in Ioc x (x + 1),
        ENNReal.ofReal ((1 / 3 : ℝ) * Real.exp (-(x + 1) ^ 2 / 2)) := by
          simp [Real.volume_Ioc]
    _ ≤ ∫⁻ u in Ioc x (x + 1), gaussianPDF 0 1 u := by
      exact setLIntegral_mono' measurableSet_Ioc fun u hu =>
        ENNReal.ofReal_le_ofReal (hpdf u hu)
    _ = gaussianReal 0 1 (Ioc x (x + 1)) :=
      (gaussianReal_apply 0 (by norm_num : (1 : NNReal) ≠ 0) _).symm
    _ ≤ _ := measure_mono fun u hu => hu.1.trans_le (le_abs_self u)

private theorem two_mul_exp_neg_four_sq_le {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.exp (-4 * (x + 1) ^ 2) ≤
      (1 / 3 : ℝ) * Real.exp (-(x + 1) ^ 2 / 2) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [Real.exp_pos (1 : ℝ)]
  have he : (6 : ℝ) ≤ Real.exp ((7 / 2 : ℝ) * (x + 1) ^ 2) := by
    refine (by linarith : (6 : ℝ) ≤ Real.exp 3).trans (Real.exp_le_exp.mpr ?_)
    nlinarith [sq_nonneg x]
  have hid : Real.exp (-(x + 1) ^ 2 / 2) =
      Real.exp (-4 * (x + 1) ^ 2) * Real.exp ((7 / 2 : ℝ) * (x + 1) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid]
  nlinarith [Real.exp_pos (-4 * (x + 1) ^ 2)]

/-- An exponential-square moment controls every absolute tail, with no
integrability assumption hidden in a totalized Bochner integral. -/
theorem measure_abs_gt_le_of_lintegral_exp_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : AEMeasurable X μ) {K : ℝ} (hK : 0 < K)
    (hpsi : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / K) ^ 2)) ∂μ ≤ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-(t / K) ^ 2)) := by
  have he : ENNReal.ofReal (Real.exp ((t / K) ^ 2)) ≠ 0 := by positivity
  have hsub : {ω | t < |X ω|} ⊆
      {ω | ENNReal.ofReal (Real.exp ((t / K) ^ 2)) ≤
        ENNReal.ofReal (Real.exp ((X ω / K) ^ 2))} := by
    intro ω hω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h : t / K ≤ |X ω| / K := div_le_div_of_nonneg_right hω.le hK.le
    rw [show |X ω| / K = |X ω / K| by rw [abs_div, abs_of_pos hK]] at h
    nlinarith [sq_abs (X ω / K), div_nonneg ht hK.le, abs_nonneg (X ω / K)]
  calc
    _ ≤ μ {ω | ENNReal.ofReal (Real.exp ((t / K) ^ 2)) ≤
        ENNReal.ofReal (Real.exp ((X ω / K) ^ 2))} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / K) ^ 2)) ∂μ) /
        ENNReal.ofReal (Real.exp ((t / K) ^ 2)) :=
      meas_ge_le_lintegral_div (by fun_prop) he ENNReal.ofReal_ne_top
    _ ≤ 2 / ENNReal.ofReal (Real.exp ((t / K) ^ 2)) :=
      ENNReal.div_le_div_right hpsi _
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _),
        div_eq_mul_inv, ← Real.exp_neg]

/-- A symmetric difference with square-exponential parameter `2K` has absolute
tails dominated by the actual random variable `4K(1+|g|)`. -/
theorem measure_abs_gt_le_gaussian_shift_of_lintegral_exp_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) {K : ℝ} (hK : 0 < K)
    (hpsi : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (2 * K)) ^ 2)) ∂μ ≤ 2)
    (t : ℝ) :
    μ {ω | t < |X ω|} ≤
      gaussianReal 0 1 {g : ℝ | t < 4 * K * (1 + |g|)} := by
  by_cases ht : t < 4 * K
  · have he : {g : ℝ | t < 4 * K * (1 + |g|)} = univ := by
      ext g
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      nlinarith [abs_nonneg g]
    rw [he, measure_univ]
    exact prob_le_one
  · have ht0 : 0 ≤ t := by linarith
    let x := t / (4 * K) - 1
    have hx : 0 ≤ x := by dsimp [x]; rw [sub_nonneg, le_div_iff₀ (by positivity)]; linarith
    have hxid : t / (2 * K) = 2 * (x + 1) := by dsimp [x]; field_simp; ring
    have he : {g : ℝ | x < |g|} = {g : ℝ | t < 4 * K * (1 + |g|)} := by
      ext g
      dsimp [x]
      constructor <;> intro h
      · have hh : t / (4 * K) < 1 + |g| := by linarith
        have hh' := (div_lt_iff₀ (by positivity : 0 < 4 * K)).mp hh
        nlinarith
      · have hh := (div_lt_iff₀ (by positivity : 0 < 4 * K)).mpr
          (show t < (1 + |g|) * (4 * K) by nlinarith)
        linarith
    calc
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(t / (2 * K)) ^ 2)) :=
        measure_abs_gt_le_of_lintegral_exp_sq hX (by positivity) hpsi ht0
      _ = ENNReal.ofReal (2 * Real.exp (-4 * (x + 1) ^ 2)) := by
        have hpow : -(2 * (x + 1)) ^ 2 = -4 * (x + 1) ^ 2 := by ring
        rw [hxid, hpow]
      _ ≤ ENNReal.ofReal ((1 / 3 : ℝ) * Real.exp (-(x + 1) ^ 2 / 2)) :=
        ENNReal.ofReal_le_ofReal (two_mul_exp_neg_four_sq_le hx)
      _ ≤ gaussianReal 0 1 {g : ℝ | x < |g|} := ofReal_exp_neg_sq_le_gaussianReal_abs_gt hx
      _ = _ := congrArg (gaussianReal 0 1) he

/-- Taking an independent difference doubles the square-exponential parameter.
The pointwise convexity bound in fact needs only the two marginal moments. -/
theorem lintegral_exp_sub_sq_le_two {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν ≤ 2) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (((p.1 - p.2) / (2 * K)) ^ 2))
      ∂ν.prod ν) ≤ 2 := by
  have hp (x y : ℝ) : Real.exp (((x - y) / (2 * K)) ^ 2) ≤
      (1 / 2 : ℝ) * (Real.exp ((x / K) ^ 2) + Real.exp ((y / K) ^ 2)) := by
    have hsq : ((x - y) / (2 * K)) ^ 2 ≤
        (1 / 2 : ℝ) * (x / K) ^ 2 + (1 / 2 : ℝ) * (y / K) ^ 2 := by
      have hid : (x - y) / (2 * K) = ((x / K) - (y / K)) / 2 := by ring
      rw [hid]
      nlinarith [sq_nonneg (x / K + y / K)]
    have hc := convexOn_exp.2 (mem_univ ((x / K) ^ 2)) (mem_univ ((y / K) ^ 2))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    refine (Real.exp_le_exp.mpr hsq).trans ?_
    simpa only [smul_eq_mul, mul_add] using hc
  have hfst : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp ((p.1 / K) ^ 2)) ∂ν.prod ν) =
      ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν := by
    rw [lintegral_prod _ (by fun_prop)]
    simp
  have hsnd : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp ((p.2 / K) ^ 2)) ∂ν.prod ν) =
      ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν := by
    rw [lintegral_prod _ (by fun_prop)]
    simp
  calc
    _ ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (1 / 2 : ℝ) *
        (ENNReal.ofReal (Real.exp ((p.1 / K) ^ 2)) +
          ENNReal.ofReal (Real.exp ((p.2 / K) ^ 2))) ∂ν.prod ν := by
      apply lintegral_mono
      intro p
      dsimp only
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact ENNReal.ofReal_le_ofReal (hp p.1 p.2)
    _ = ENNReal.ofReal (1 / 2 : ℝ) *
        ((∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν) +
          ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν) := by
      rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop), hfst, hsnd]
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * (2 + 2) := by gcongr
    _ = 2 := by
      norm_num [ENNReal.ofReal_div_of_pos]
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ← mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by simp), one_mul]

end NLAlib
