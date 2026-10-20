import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Independent-copy exponential entropy

The generic entropy method bounds the entropy of an exponential by its
exponentially weighted positive squared independent-copy difference.
All statements concern ordinary real functions and actual probability laws.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Real

/-- The symmetric exponential covariance is controlled by oriented positive
squared differences. This is the scalar step of the independent-copy entropy method. -/
theorem exp_mul_sub_mul_sub_le_posPart_sq {a b s : ℝ} (hs : 0 ≤ s) :
    (exp (s * a) - exp (s * b)) * (s * (a - b)) ≤
      s ^ 2 * (exp (s * a) * max (a - b) 0 ^ 2 +
        exp (s * b) * max (b - a) 0 ^ 2) := by
  have hscalar (u v : ℝ) : exp u - exp v ≤ exp u * (u - v) := by
    have h := mul_le_mul_of_nonneg_left (add_one_le_exp (v - u)) (exp_pos u).le
    have he : exp u * exp (v - u) = exp v := by
      rw [← exp_add]
      congr 1
      ring
    rw [he] at h
    nlinarith
  rcases le_total b a with hab | hab
  · rw [max_eq_left (sub_nonneg.mpr hab), max_eq_right (sub_nonpos.mpr hab)]
    have h := mul_le_mul_of_nonneg_right (hscalar (s * a) (s * b))
      (mul_nonneg hs (sub_nonneg.mpr hab))
    nlinarith
  · rw [max_eq_right (sub_nonpos.mpr hab), max_eq_left (sub_nonneg.mpr hab)]
    have h := mul_le_mul_of_nonneg_right (hscalar (s * b) (s * a))
      (mul_nonneg hs (sub_nonneg.mpr hab))
    nlinarith

/-- A bounded absolute value gives a uniform exponential bound at every real parameter. -/
theorem exp_mul_le_exp_abs_mul_of_abs_le {u s M : ℝ} (hu : |u| ≤ M) :
    Real.exp (s * u) ≤ Real.exp (|s| * M) := by
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hu (abs_nonneg s))

end Real

namespace MeasureTheory

/-- On a probability space, entropy of an exponential is bounded by its
actual independently resampled positive squared difference. The hypotheses
are integrability of the displayed elementary functions, not an entropy bound.
Source: the independent-copy step in the entropy method, Boucheron--Lugosi--Massart
2013, Chapter 6. -/
theorem entropy_exp_mul_le_integral_posPart_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hf : Integrable f μ)
    (hY : Integrable (fun x => Real.exp (s * f x)) μ)
    (hW : Integrable (fun x => f x * Real.exp (s * f x)) μ)
    (hU : Integrable (fun q : Ω × Ω =>
      Real.exp (s * f q.1) * max (f q.1 - f q.2) 0 ^ 2) (μ.prod μ)) :
    (∫ x, s * f x * Real.exp (s * f x) ∂μ) -
      (∫ x, Real.exp (s * f x) ∂μ) * Real.log (∫ x, Real.exp (s * f x) ∂μ) ≤
      s ^ 2 * ∫ q : Ω × Ω,
        Real.exp (s * f q.1) * max (f q.1 - f q.2) 0 ^ 2 ∂(μ.prod μ) := by
  let Y : Ω → ℝ := fun x => Real.exp (s * f x)
  let W : Ω → ℝ := fun x => f x * Y x
  let U : Ω × Ω → ℝ := fun q => Y q.1 * max (f q.1 - f q.2) 0 ^ 2
  let G : Ω × Ω → ℝ := fun q => (Y q.1 - Y q.2) * (f q.1 - f q.2)
  have hW' : Integrable W μ := hW
  have hY' : Integrable Y μ := hY
  have hU' : Integrable U (μ.prod μ) := hU
  have hG : Integrable G (μ.prod μ) := by
    have h := (((hW'.comp_fst μ).add (hW'.comp_snd μ)).sub
      (hY'.mul_prod hf)).sub (hf.mul_prod hY')
    convert h using 1
    ext q
    dsimp [G, W]
    ring
  have hGint : ∫ q, G q ∂(μ.prod μ) =
      2 * ((∫ x, W x ∂μ) - (∫ x, Y x ∂μ) * (∫ x, f x ∂μ)) := by
    have he : G = fun q : Ω × Ω =>
        (W q.1 + W q.2 - Y q.1 * f q.2) - f q.1 * Y q.2 := by
      ext q
      dsimp [G, W]
      ring
    rw [he,
      integral_sub (f := fun q : Ω × Ω => W q.1 + W q.2 - Y q.1 * f q.2)
        (g := fun q : Ω × Ω => f q.1 * Y q.2)
        (((hW'.comp_fst μ).add (hW'.comp_snd μ)).sub (hY'.mul_prod hf)) (hf.mul_prod hY'),
      integral_sub (f := fun q : Ω × Ω => W q.1 + W q.2)
        (g := fun q : Ω × Ω => Y q.1 * f q.2)
        ((hW'.comp_fst μ).add (hW'.comp_snd μ)) (hY'.mul_prod hf),
      integral_add (f := fun q : Ω × Ω => W q.1) (g := fun q : Ω × Ω => W q.2)
        (hW'.comp_fst μ) (hW'.comp_snd μ),
      integral_fun_fst, integral_fun_snd, integral_prod_mul, integral_prod_mul]
    simp only [probReal_univ, one_smul]
    ring
  have hpair := integral_mono (hG.const_mul s)
    ((hU'.add hU'.swap).const_mul (s ^ 2)) (fun q : Ω × Ω => by
      have hp := Real.exp_mul_sub_mul_sub_le_posPart_sq (a := f q.1) (b := f q.2) hs
      dsimp [G, U, Y]
      nlinarith)
  rw [integral_const_mul, integral_const_mul] at hpair
  change s * (∫ q, G q ∂μ.prod μ) ≤
    s ^ 2 * ∫ q, U q + U q.swap ∂μ.prod μ at hpair
  rw [integral_add (f := U) (g := fun q => U q.swap) hU' hU'.swap,
    integral_prod_swap, hGint] at hpair
  have hJ : Real.exp (s * ∫ x, f x ∂μ) ≤ ∫ x, Y x ∂μ := by
    simpa only [integral_const_mul, Y] using
      convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
        isClosed_univ (ae_of_all μ fun _ => Set.mem_univ _) (hf.const_mul s) hY
  have hpos : 0 < ∫ x, Y x ∂μ := (Real.exp_pos _).trans_le hJ
  have hlog : s * (∫ x, f x ∂μ) ≤ Real.log (∫ x, Y x ∂μ) :=
    (Real.le_log_iff_exp_le hpos).mpr hJ
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have hleft : (∫ x, s * f x * Real.exp (s * f x) ∂μ) = s * ∫ x, W x ∂μ := by
    rw [← integral_const_mul]
    congr 1
    ext x
    dsimp [W, Y]
    ring
  rw [hleft]
  change s * (∫ x, W x ∂μ) - (∫ x, Y x ∂μ) * Real.log (∫ x, Y x ∂μ) ≤
    s ^ 2 * ∫ q, U q ∂(μ.prod μ)
  nlinarith

private theorem integrable_of_uniform_abs_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) : Integrable f μ := by
  exact (integrable_const M).mono' hf.aestronglyMeasurable
    (ae_of_all μ fun x => by simpa only [Real.norm_eq_abs] using hM x)


private theorem exp_mul_posPart_sq_abs_le {a b M s : ℝ} (hM : 0 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |Real.exp (s * a) * max (a - b) 0 ^ 2| ≤
      Real.exp (|s| * M) * (2 * M) ^ 2 := by
  have hd : max (a - b) 0 ≤ 2 * M := by
    apply max_le
    · linarith [le_abs_self (a - b), abs_sub a b]
    · positivity
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul (Real.exp_mul_le_exp_abs_mul_of_abs_le ha)
    ((sq_le_sq₀ (le_max_right _ _) (by positivity)).mpr hd)
    (sq_nonneg _) (Real.exp_pos _).le

/-- A bounded measurable pair has an integrable exponentially weighted squared
positive difference on every finite measure space. -/
theorem integrable_exp_mul_posPart_sub_sq_of_abs_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    {M : ℝ} (hM : 0 ≤ M) (hfb : ∀ x, |f x| ≤ M) (hgb : ∀ x, |g x| ≤ M)
    (s : ℝ) : Integrable (fun x => Real.exp (s * f x) * max (f x - g x) 0 ^ 2) μ := by
  apply integrable_of_uniform_abs_bound (by fun_prop)
    (Real.exp (|s| * M) * (2 * M) ^ 2)
  exact fun x => exp_mul_posPart_sq_abs_le hM (hfb x) (hgb x)

/-- The bounded measurable independent-copy entropy inequality. All
integrability hypotheses are derived from the actual bound on `f`. -/
theorem entropy_exp_mul_le_integral_posPart_sq_of_bounded
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hfm : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M) {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, s * f x * Real.exp (s * f x) ∂μ) -
      (∫ x, Real.exp (s * f x) ∂μ) * Real.log (∫ x, Real.exp (s * f x) ∂μ) ≤
      s ^ 2 * ∫ q : Ω × Ω,
        Real.exp (s * f q.1) * max (f q.1 - f q.2) 0 ^ 2 ∂(μ.prod μ) := by
  have hf := integrable_of_uniform_abs_bound hfm M hbound (μ := μ)
  have hY : Integrable (fun x => Real.exp (s * f x)) μ := integrable_of_uniform_abs_bound
    (Real.measurable_exp.comp ((measurable_const (a := s)).mul hfm)) (Real.exp (|s| * M))
    (fun x => by simpa only [abs_of_pos (Real.exp_pos _)] using Real.exp_mul_le_exp_abs_mul_of_abs_le (s := s) (hbound x))
    (μ := μ)
  have hW : Integrable (fun x => f x * Real.exp (s * f x)) μ := by
    apply integrable_of_uniform_abs_bound (by fun_prop) (M * Real.exp (|s| * M))
    intro x
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hbound x) (Real.exp_mul_le_exp_abs_mul_of_abs_le (hbound x))
      (Real.exp_pos _).le hM
  have hU : Integrable (fun q : Ω × Ω =>
      Real.exp (s * f q.1) * max (f q.1 - f q.2) 0 ^ 2) (μ.prod μ) :=
    integrable_exp_mul_posPart_sub_sq_of_abs_le (fun q : Ω × Ω => f q.1) (fun q : Ω × Ω => f q.2)
      (hfm.comp measurable_fst) (hfm.comp measurable_snd) hM
      (fun q => hbound q.1) (fun q => hbound q.2) s
  exact entropy_exp_mul_le_integral_posPart_sq μ f hs hf hY hW hU


end MeasureTheory
