import NLAlib.Gaussian.PositiveMoments
import NLAlib.Gaussian.Invariance
import NLAlib.Gaussian.Extreme.LinearForms
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Logarithmic Gaussian starting overlap

Gaussian random-start eigenvalue bounds integrate the logarithm of the tail/head
energy ratio, rather than its divergent first moment.
Source: manuscript `rt:log-moments`; KW (1992), random-start overlap.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace NLAlib

/-- The standard Gaussian density is bounded by one half. This deliberately coarse
constant is enough for the logarithmic-overlap bounds. Source: manuscript
`rt:log-moments`, Gaussian small-ball calculation. -/
theorem gaussianPDFReal_zero_one_le_half (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 / 2 := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hden : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
    have hn := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith [Real.pi_gt_three]
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
  exact (mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
    (by simpa only [mul_one] using hinv)

/-- A standard Gaussian has absolute small-ball probability at most the radius.
Source: manuscript `rt:log-moments`; the coarse constant one preserves its printed
overlap tail and both logarithmic moment constants. The zero-radius case is included. -/
theorem gaussianReal_abs_le_le_ofReal {a : ℝ} (_ha : 0 ≤ a) :
    gaussianReal 0 1 {x : ℝ | |x| ≤ a} ≤ ENNReal.ofReal a := by
  have hSet : {x : ℝ | |x| ≤ a} = Icc (-a) a := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  rw [hSet, gaussianReal_apply 0 (by norm_num : (1 : NNReal) ≠ 0)]
  calc
    (∫⁻ x in Icc (-a) a, gaussianPDF 0 1 x) ≤
        ∫⁻ _ in Icc (-a) a, ENNReal.ofReal (1 / 2 : ℝ) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_zero_one_le_half x)
    _ = ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (2 * a) := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      congr 2
      ring
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      ring

/-- The logarithm of one plus tail/head Gaussian energy; the head-zero null set
uses the totalized real division convention. Source: manuscript `rt:log-moments`. -/
def gaussianLogOverlap {n : ℕ} (g : Fin (n + 1) → ℝ) : ℝ :=
  Real.log (1 + (∑ j : Fin n, g j.succ ^ 2) / (g 0) ^ 2)

/-- The logarithmic overlap is nonnegative at every vector, including a zero head.
Source: manuscript `rt:log-moments`, nonnegative tail-integration variable. -/
theorem gaussianLogOverlap_nonneg {n : ℕ} (g : Fin (n + 1) → ℝ) :
    0 ≤ gaussianLogOverlap g := by
  apply Real.log_nonneg
  have h : 0 ≤ (∑ j : Fin n, g j.succ ^ 2) / (g 0) ^ 2 :=
    div_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) (sq_nonneg _)
  linarith

/-- The logarithmic overlap is measurable on the coordinate Gaussian space.
Source: manuscript `rt:log-moments`, scalar tail-integration measurability. -/
theorem measurable_gaussianLogOverlap (n : ℕ) : Measurable (@gaussianLogOverlap n) := by
  unfold gaussianLogOverlap
  fun_prop

/-- A Gaussian head denominator gives a square-root upper tail for a fixed
nonnegative tail energy. Source: manuscript `rt:log-moments`, conditional small ball. -/
theorem gaussianReal_div_sq_gt_le_ofReal_sqrt {s u : ℝ} (hs : 0 ≤ s) (hu : 0 < u) :
    gaussianReal 0 1 {x : ℝ | u < s / x ^ 2} ≤ ENNReal.ofReal (Real.sqrt (s / u)) := by
  apply (measure_mono (show {x : ℝ | u < s / x ^ 2} ⊆
      {x : ℝ | |x| ≤ Real.sqrt (s / u)} from ?_)).trans
      (gaussianReal_abs_le_le_ofReal (Real.sqrt_nonneg _))
  intro x hx
  change u < s / x ^ 2 at hx
  by_cases hx0 : x = 0
  · simp only [hx0, zero_pow two_ne_zero, div_zero] at hx
    linarith
  · apply (Real.le_sqrt (abs_nonneg x) (div_nonneg hs hu.le)).mpr
    rw [sq_abs, le_div_iff₀ hu]
    simpa only [mul_comm] using ((lt_div_iff₀ (sq_pos_of_ne_zero hx0)).mp hx).le

/-- The square root of the Gaussian tail energy is integrable in every dimension,
including dimension zero. Source: Gaussian finite radial moments; `rt:log-moments`. -/
theorem integrable_sqrt_sum_sq_pi_gaussianReal (n : ℕ) :
    Integrable (fun g : Fin n → ℝ => Real.sqrt (∑ i, g i ^ 2))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  simpa only [Real.sqrt_eq_rpow] using
    integrable_rpow_sum_sq_pi_gaussianReal n (1 / 2) (by norm_num)

/-- The expected square root of a Gaussian tail energy is at most the square root
of its dimension. Source: manuscript `rt:log-moments`, scalar Cauchy--Schwarz;
reuses the established Gaussian-row norm expectation. -/
theorem integral_sqrt_sum_sq_pi_gaussianReal_le (n : ℕ) :
    (∫ g : Fin n → ℝ, Real.sqrt (∑ i, g i ^ 2)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) ≤ Real.sqrt n := by
  have hmp : MeasurePreserving (fun G : Fin 1 → Fin n → ℝ => G 0)
      (gaussianMatrix 1 n) (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    measurePreserving_eval (fun _ : Fin 1 => Measure.pi fun _ : Fin n => gaussianReal 0 1) 0
  have hm : Measurable (fun g : Fin n → ℝ => Real.sqrt (∑ i, g i ^ 2)) := by fun_prop
  have h := integral_map (μ := gaussianMatrix 1 n) hmp.measurable.aemeasurable
    (f := fun g : Fin n → ℝ => Real.sqrt (∑ i, g i ^ 2)) hm.aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h.trans_le (integral_sqrt_sum_sq_gaussianMatrix_entry_le (fun i : Fin n => i))

/-- Independent Gaussian head and tail coordinates have the explicit square-root
energy-ratio tail. Source: manuscript `rt:log-moments`, conditional small-ball step.
No inverse-head moment is integrated. -/
theorem prod_gaussianReal_energy_ratio_gt_le (n : ℕ) {u : ℝ} (hu : 0 < u) :
    ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))
      {p : ℝ × (Fin n → ℝ) | u < (∑ i, p.2 i ^ 2) / p.1 ^ 2} ≤
        ENNReal.ofReal (Real.sqrt (n / u)) := by
  let μ := Measure.pi fun _ : Fin n => gaussianReal 0 1
  have hm : MeasurableSet {p : ℝ × (Fin n → ℝ) | u < (∑ i, p.2 i ^ 2) / p.1 ^ 2} := by
    apply measurableSet_lt measurable_const
    fun_prop
  rw [Measure.prod_apply_symm hm]
  change (∫⁻ g : Fin n → ℝ, gaussianReal 0 1 {x | u < (∑ i, g i ^ 2) / x ^ 2} ∂μ) ≤ _
  have hi := (integrable_sqrt_sum_sq_pi_gaussianReal n).div_const (Real.sqrt u)
  calc
    (∫⁻ g : Fin n → ℝ, gaussianReal 0 1 {x | u < (∑ i, g i ^ 2) / x ^ 2} ∂μ) ≤
        ∫⁻ g : Fin n → ℝ, ENNReal.ofReal (Real.sqrt (∑ i, g i ^ 2) / Real.sqrt u) ∂μ := by
      apply lintegral_mono
      intro g
      simpa only [Real.sqrt_div (Finset.sum_nonneg fun i _ => sq_nonneg _)] using
        gaussianReal_div_sq_gt_le_ofReal_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _) hu
    _ = ENNReal.ofReal ((∫ g : Fin n → ℝ, Real.sqrt (∑ i, g i ^ 2) ∂μ) / Real.sqrt u) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ fun g => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), integral_div]
    _ ≤ ENNReal.ofReal (Real.sqrt (n : ℝ) / Real.sqrt u) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (integral_sqrt_sum_sq_pi_gaussianReal_le n) (Real.sqrt_nonneg u))
    _ = _ := by rw [Real.sqrt_div (Nat.cast_nonneg n)]

/-- The coordinate Gaussian vector has the same energy-ratio tail after separating
its first coordinate from the independent tail. Source: manuscript `rt:log-moments`;
Mathlib's measure-preserving finite Gaussian coordinate split. -/
theorem pi_gaussianReal_energy_ratio_gt_le (n : ℕ) {u : ℝ} (hu : 0 < u) :
    (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)
      {g | u < (∑ i : Fin n, g i.succ ^ 2) / (g 0) ^ 2} ≤
        ENNReal.ofReal (Real.sqrt (n / u)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0
  have he : (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)
      {g | u < (∑ i : Fin n, g i.succ ^ 2) / (g 0) ^ 2} =
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))
        {p : ℝ × (Fin n → ℝ) | u < (∑ i, p.2 i ^ 2) / p.1 ^ 2} := by
    rw [← hmp.map_eq, e.map_apply]
    congr 1
  rw [he]
  exact prod_gaussianReal_energy_ratio_gt_le n hu

/-- The Gaussian logarithmic overlap has the explicit exponential upper tail beyond
`log(2N)`. Source: manuscript `rt:log-moments`; the dimension is `N = n+1` and all
zero-head values use the specified null-set convention. -/
theorem pi_gaussianReal_logOverlap_gt_le (n : ℕ) {t : ℝ}
    (ht : Real.log (2 * ((n + 1 : ℕ) : ℝ)) ≤ t) :
    (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) {g | t < gaussianLogOverlap g} ≤
      ENNReal.ofReal (Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) * Real.exp (-t / 2)) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hExp : 2 * ((n + 1 : ℕ) : ℝ) ≤ Real.exp t := by
    have h := Real.exp_le_exp.mpr ht
    rwa [Real.exp_log (mul_pos (by norm_num) hn)] at h
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hExp2 : (2 : ℝ) ≤ Real.exp t := by push_cast at hExp; linarith
  have hu : 0 < Real.exp t - 1 := by linarith
  have he : {g : Fin (n + 1) → ℝ | t < gaussianLogOverlap g} =
      {g | Real.exp t - 1 < (∑ i : Fin n, g i.succ ^ 2) / (g 0) ^ 2} := by
    ext g
    change (t < Real.log (1 + (∑ i : Fin n, g i.succ ^ 2) / (g 0) ^ 2)) ↔
      (Real.exp t - 1 < (∑ i : Fin n, g i.succ ^ 2) / (g 0) ^ 2)
    have hR : 0 ≤ (∑ i : Fin n, g i.succ ^ 2) / (g 0) ^ 2 :=
      div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)
    rw [Real.lt_log_iff_exp_lt (by linarith : 0 < 1 + (∑ i : Fin n, g i.succ ^ 2) / (g 0) ^ 2)]
    constructor <;> intro h <;> linarith
  have hdiv : (n : ℝ) / (Real.exp t - 1) ≤ (2 * ((n + 1 : ℕ) : ℝ)) / Real.exp t := by
    have h1 : 1 / (Real.exp t - 1) ≤ 2 / Real.exp t := by
      apply (div_le_div_iff₀ hu (Real.exp_pos t)).mpr
      linarith
    calc (n : ℝ) / (Real.exp t - 1) = n * (1 / (Real.exp t - 1)) := by ring
      _ ≤ n * (2 / Real.exp t) := mul_le_mul_of_nonneg_left h1 hn0
      _ = (2 * n) / Real.exp t := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by push_cast; linarith) (Real.exp_pos t).le
  have hs := Real.sqrt_le_sqrt hdiv
  rw [Real.sqrt_div (by positivity : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ)), ← Real.exp_half] at hs
  have hbound : Real.sqrt (n / (Real.exp t - 1)) ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) * Real.exp (-t / 2) := by
    simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_mul] using hs
  rw [he]
  exact (pi_gaussianReal_energy_ratio_gt_le n hu).trans (ENNReal.ofReal_le_ofReal hbound)

/-- The logarithmic overlap is the logarithm of total energy divided by head energy.
The identity also holds on the null zero-head set because both totalized logarithms
are zero. Source: manuscript `rt:log-moments`, `L=-log w_1`. -/
theorem gaussianLogOverlap_eq_log_sum_div_sq {n : ℕ} (g : Fin (n + 1) → ℝ) :
    gaussianLogOverlap g = Real.log ((∑ i, g i ^ 2) / (g 0) ^ 2) := by
  by_cases hg : g 0 = 0
  · simp only [gaussianLogOverlap, hg, zero_pow two_ne_zero, div_zero, add_zero,
      Real.log_one, Real.log_zero]
  · unfold gaussianLogOverlap
    rw [Fin.sum_univ_succ]
    congr 1
    field_simp

end NLAlib
