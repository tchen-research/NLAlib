import NLAlib.Concentration.Scalar.EntropyTensorization
import NLAlib.ForMathlib.Analysis.Real
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Entropy tensorization for nonnegative functions

Atlas: `entropy-tensorization`. Extends Ledoux, Prop. 5.6 and
Boucheron--Lugosi--Massart 2013, Thm. 4.10 from positive to nonnegative
functions, retaining NLAlib's literal entropy expression. The proof uses
Mathlib's Jensen inequality for `x log x`, one-coordinate conditional means,
and the uniform regularization bound already in NLAlib.

The local registry at `E:/Database-RA01-reviewed-2026-10-06` was consulted:
the conditional-mean coupling of `PP-03/T-0027` is restricted to signed
bucket selectors and is not used as an arbitrary-measure entropy theorem.
No registry claim is promoted or used beyond its recorded scope.
-/

noncomputable section
open MeasureTheory Filter

namespace NLAlib

/-- Integrability of a nonnegative function follows from integrability of
`f log f` on a finite measure space. Source: Mathlib's
`Real.self_sub_one_le_mul_log`. Atlas: `entropy-tensorization`. -/
theorem integrable_of_nonneg_mul_log_integrable {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {f : α → ℝ} (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hlog : Integrable (fun x => f x * Real.log (f x)) ν) :
    Integrable f ν := by
  refine Integrable.mono' (hlog.abs.add (integrable_const (1 : ℝ)))
    hfm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (hf x)]
  have h := Real.self_sub_one_le_mul_log (hf x)
  have ha := le_abs_self (f x * Real.log (f x))
  linarith

/-- Jensen's inequality for `x log x`, with zero values allowed. Source:
Mathlib's `Real.convexOn_mul_log` and `ConvexOn.map_integral_le`.
Atlas: `entropy-tensorization`. -/
theorem mul_log_integral_le_integral_mul_log_of_nonneg {α : Type*}
    [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hint : Integrable f ν)
    (hlog : Integrable (fun x => f x * Real.log (f x)) ν) :
    (∫ x, f x ∂ν) * Real.log (∫ x, f x ∂ν) ≤ ∫ x, f x * Real.log (f x) ∂ν :=
  Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
    isClosed_Ici (ae_of_all _ fun x => hf x) hint hlog

/-- Positive regularization preserves integrability of `f log f`, with a
dominating function independent of `0 < δ ≤ 1`. Source: NLAlib's
`abs_add_mul_log_add_le`. Atlas: `entropy-tensorization`. -/
theorem integrable_mul_log_add_of_nonneg {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {f : α → ℝ} (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hint : Integrable f ν)
    (hlog : Integrable (fun x => f x * Real.log (f x)) ν)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Integrable (fun x => (f x + δ) * Real.log (f x + δ)) ν := by
  refine Integrable.mono' ((hlog.abs.add hint).add (integrable_const (2 : ℝ)))
    (Real.continuous_mul_log.measurable.comp (hfm.add measurable_const)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  exact abs_add_mul_log_add_le (f x) δ (hf x) hδ hδ1

/-- Dominated convergence for the entropy integrand under positive shifts
tending to zero, with actual integrability throughout. Source: dominated
convergence and NLAlib's `abs_add_mul_log_add_le`.
Atlas: `entropy-tensorization`. -/
theorem tendsto_integral_mul_log_add_of_nonneg {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {f : α → ℝ} (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hint : Integrable f ν)
    (hlog : Integrable (fun x => f x * Real.log (f x)) ν)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n ≤ 1)
    (hδlim : Tendsto δ atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, (f x + δ n) * Real.log (f x + δ n) ∂ν)
      atTop (nhds (∫ x, f x * Real.log (f x) ∂ν)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun x => |f x * Real.log (f x)| + f x + 2)
    (fun n => (Real.continuous_mul_log.measurable.comp
      (hfm.add measurable_const)).aestronglyMeasurable)
    ((hlog.abs.add hint).add (integrable_const (2 : ℝ)))
    (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · rw [Real.norm_eq_abs]
    exact abs_add_mul_log_add_le (f x) (δ n) (hf x) (hδ n) (hδ1 n)
  · have hlim : Tendsto (fun n => f x + δ n) atTop (nhds (f x)) := by
      simpa using (tendsto_const_nhds (x := f x)).add hδlim
    exact (Real.continuous_mul_log.tendsto (f x)).comp hlim

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]

omit [Fintype ι] in
/-- A one-coordinate conditional mean is measurable. Source: Mathlib's
`StronglyMeasurable.integral_prod_right'` applied to coordinate resampling.
Atlas: `entropy-tensorization`. -/
theorem measurable_integral_update_pi (i : ι) {f : (ι → Ω) → ℝ}
    (hfm : Measurable f) :
    Measurable (fun x => ∫ t, f (Function.update x i t) ∂(μ i)) := by
  exact (StronglyMeasurable.integral_prod_right'
    (f := fun p : (ι → Ω) × Ω => f (Function.update p.1 i p.2))
    (hfm.comp measurable_update').stronglyMeasurable).measurable

/-- `E_i f log(E_i f)` is integrable whenever a nonnegative `f` and its
entropy integrand are integrable. The proof uses conditional Jensen and
the lower bound `x log x ≥ -1`. Source: Jensen's inequality and NLAlib's
one-coordinate Fubini lemmas. Atlas: `entropy-tensorization`. -/
theorem integrable_mul_log_integral_update_of_nonneg (i : ι)
    {f : (ι → Ω) → ℝ} (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hint : Integrable f (Measure.pi μ))
    (hlog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi μ)) :
    Integrable (fun x => (∫ t, f (Function.update x i t) ∂(μ i)) *
      Real.log (∫ t, f (Function.update x i t) ∂(μ i))) (Measure.pi μ) := by
  have hmeas := measurable_integral_update_pi μ i hfm
  have hupper := integrable_integral_update_pi μ i hlog
  refine Integrable.mono' (hupper.abs.add (integrable_const (1 : ℝ)))
    (Real.continuous_mul_log.measurable.comp hmeas).aestronglyMeasurable ?_
  filter_upwards [ae_integrable_comp_update_pi μ i hint,
    ae_integrable_comp_update_pi μ i hlog] with x h1 h2
  have hu := mul_log_integral_le_integral_mul_log_of_nonneg
    (fun t => hf (Function.update x i t)) h1 h2
  have hm0 : 0 ≤ ∫ t, f (Function.update x i t) ∂(μ i) :=
    integral_nonneg fun t => hf _
  have hl := Real.self_sub_one_le_mul_log hm0
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_le]
  constructor
  · have ha := abs_nonneg (∫ t,
      f (Function.update x i t) * Real.log (f (Function.update x i t)) ∂(μ i))
    linarith
  · have ha := le_abs_self (∫ t,
      f (Function.update x i t) * Real.log (f (Function.update x i t)) ∂(μ i))
    linarith

/-- The actual one-coordinate entropy is integrable, also when `f` has
zeros. Source: conditional Jensen and one-coordinate Fubini.
Atlas: `entropy-tensorization`. -/
theorem integrable_entropy_update_of_nonneg (i : ι) {f : (ι → Ω) → ℝ}
    (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hint : Integrable f (Measure.pi μ))
    (hlog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi μ)) :
    Integrable (fun x => (∫ t,
      f (Function.update x i t) * Real.log (f (Function.update x i t)) ∂(μ i)) -
        (∫ t, f (Function.update x i t) ∂(μ i)) *
          Real.log (∫ t, f (Function.update x i t) ∂(μ i))) (Measure.pi μ) :=
  (integrable_integral_update_pi μ i hlog).sub
    (integrable_mul_log_integral_update_of_nonneg μ i hfm hf hint hlog)

/-- Integrated local entropy equals global `E[f log f]` minus the entropy
integrand of the conditional mean. All integrability requirements are
proved from the nonnegative-function hypotheses. Source: conditional
Jensen and one-coordinate Fubini. Atlas: `entropy-tensorization`. -/
theorem integral_entropy_update_eq_sub_integral_mul_log_mean (i : ι)
    {f : (ι → Ω) → ℝ} (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hint : Integrable f (Measure.pi μ))
    (hlog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi μ)) :
    (∫ x, ((∫ t, f (Function.update x i t) * Real.log (f (Function.update x i t)) ∂(μ i)) -
      (∫ t, f (Function.update x i t) ∂(μ i)) *
        Real.log (∫ t, f (Function.update x i t) ∂(μ i))) ∂(Measure.pi μ)) =
      (∫ x, f x * Real.log (f x) ∂(Measure.pi μ)) -
        ∫ x, (∫ t, f (Function.update x i t) ∂(μ i)) *
          Real.log (∫ t, f (Function.update x i t) ∂(μ i)) ∂(Measure.pi μ) := by
  rw [integral_sub (integrable_integral_update_pi μ i hlog)
    (integrable_mul_log_integral_update_of_nonneg μ i hfm hf hint hlog),
    integral_integral_update_pi μ i hlog]

/-- Entropy tensorizes for a measurable nonnegative function on a finite
product of probability spaces, assuming only integrability of `f log f`.
Integrability of `f`, of conditional-mean entropy integrands, and of local
entropies is derived, so this is an actual expectation bound with zeros
allowed. Source: Ledoux, Prop. 5.6; Boucheron--Lugosi--Massart 2013,
Thm. 4.10, obtained from NLAlib's positive theorem by conditional Jensen
and dominated convergence. Atlas: `entropy-tensorization`.
atlas: entropy-tensorization -/
theorem entropy_pi_le_sum_integral_entropy_update_of_nonneg
    (f : (ι → Ω) → ℝ) (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (hlog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi μ)) :
    ∫ x, f x * Real.log (f x) ∂(Measure.pi μ)
      - (∫ x, f x ∂(Measure.pi μ)) * Real.log (∫ x, f x ∂(Measure.pi μ))
      ≤ ∑ i, ∫ x, (∫ t,
          f (Function.update x i t) * Real.log (f (Function.update x i t)) ∂(μ i))
        - (∫ t, f (Function.update x i t) ∂(μ i)) *
          Real.log (∫ t, f (Function.update x i t) ∂(μ i)) ∂(Measure.pi μ) := by
  have hint := integrable_of_nonneg_mul_log_integrable hfm hf hlog
  let mean : ι → (ι → Ω) → ℝ := fun i x => ∫ t, f (Function.update x i t) ∂(μ i)
  have hmeanm (i : ι) : Measurable (mean i) := measurable_integral_update_pi μ i hfm
  have hmeann (i : ι) (x : ι → Ω) : 0 ≤ mean i x := integral_nonneg fun t => hf _
  have hmeani (i : ι) : Integrable (mean i) (Measure.pi μ) :=
    integrable_integral_update_pi μ i hint
  have hmeanl (i : ι) : Integrable (fun x => mean i x * Real.log (mean i x)) (Measure.pi μ) :=
    integrable_mul_log_integral_update_of_nonneg μ i hfm hf hint hlog
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ 1 := by
    dsimp [δ]
    rw [div_le_one (by positivity)]
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hδlim : Tendsto δ atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hshiftm (n : ℕ) : Measurable (fun x => f x + δ n) := hfm.add measurable_const
  have hshiftn (n : ℕ) (x : ι → Ω) : 0 ≤ f x + δ n := by
    have h1 := hf x
    have h2 := hδpos n
    linarith
  have hshiftp (n : ℕ) (x : ι → Ω) : 0 < f x + δ n := by
    have h1 := hf x
    have h2 := hδpos n
    linarith
  have hshifti (n : ℕ) : Integrable (fun x => f x + δ n) (Measure.pi μ) :=
    hint.add (integrable_const _)
  have hshiftl (n : ℕ) :
      Integrable (fun x => (f x + δ n) * Real.log (f x + δ n)) (Measure.pi μ) :=
    integrable_mul_log_add_of_nonneg hfm hf hint hlog (hδpos n) (hδle n)
  have hshiftint (n : ℕ) : (∫ x, f x + δ n ∂(Measure.pi μ)) =
      (∫ x, f x ∂(Measure.pi μ)) + δ n := by
    rw [integral_add hint (integrable_const _)]
    simp
  have hlocal (i : ι) (n : ℕ) :
      (∫ x, (∫ t, (f (Function.update x i t) + δ n) *
          Real.log (f (Function.update x i t) + δ n) ∂(μ i)) -
        (∫ t, f (Function.update x i t) + δ n ∂(μ i)) *
          Real.log (∫ t, f (Function.update x i t) + δ n ∂(μ i)) ∂(Measure.pi μ)) =
      (∫ x, (f x + δ n) * Real.log (f x + δ n) ∂(Measure.pi μ)) -
        ∫ x, (mean i x + δ n) * Real.log (mean i x + δ n) ∂(Measure.pi μ) := by
    rw [integral_entropy_update_eq_sub_integral_mul_log_mean μ i
      (hshiftm n) (hshiftn n) (hshifti n) (hshiftl n)]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_integrable_comp_update_pi μ i hint] with x hx
    have he : (∫ t, f (Function.update x i t) + δ n ∂(μ i)) = mean i x + δ n := by
      rw [integral_add hx (integrable_const _)]
      simp only [integral_const]
      simp [mean]
    rw [he]
  have hpoint (n : ℕ) :
      (∫ x, (f x + δ n) * Real.log (f x + δ n) ∂(Measure.pi μ)) -
        ((∫ x, f x ∂(Measure.pi μ)) + δ n) *
          Real.log ((∫ x, f x ∂(Measure.pi μ)) + δ n) ≤
      ∑ i, ((∫ x, (f x + δ n) * Real.log (f x + δ n) ∂(Measure.pi μ)) -
        ∫ x, (mean i x + δ n) * Real.log (mean i x + δ n) ∂(Measure.pi μ)) := by
    have h := entropy_pi_le_sum_integral_entropy_update μ
      (fun x => f x + δ n) (hshiftm n) (hshiftp n) (hshifti n) (hshiftl n)
    rw [hshiftint n] at h
    simpa only [hlocal] using h
  have hT := tendsto_integral_mul_log_add_of_nonneg hfm hf hint hlog δ hδpos hδle hδlim
  have hM : Tendsto (fun n => ((∫ x, f x ∂(Measure.pi μ)) + δ n) *
      Real.log ((∫ x, f x ∂(Measure.pi μ)) + δ n)) atTop
      (nhds ((∫ x, f x ∂(Measure.pi μ)) * Real.log (∫ x, f x ∂(Measure.pi μ)))) := by
    have hlim : Tendsto (fun n => (∫ x, f x ∂(Measure.pi μ)) + δ n) atTop
        (nhds (∫ x, f x ∂(Measure.pi μ))) := by
      simpa using (tendsto_const_nhds (x := ∫ x, f x ∂(Measure.pi μ))).add hδlim
    exact (Real.continuous_mul_log.tendsto _).comp hlim
  have hR : Tendsto (fun n => ∑ i,
      ((∫ x, (f x + δ n) * Real.log (f x + δ n) ∂(Measure.pi μ)) -
        ∫ x, (mean i x + δ n) * Real.log (mean i x + δ n) ∂(Measure.pi μ))) atTop
      (nhds (∑ i, ((∫ x, f x * Real.log (f x) ∂(Measure.pi μ)) -
        ∫ x, mean i x * Real.log (mean i x) ∂(Measure.pi μ)))) := by
    exact tendsto_finsetSum Finset.univ fun i _ => hT.sub
      (tendsto_integral_mul_log_add_of_nonneg (hmeanm i) (hmeann i) (hmeani i)
        (hmeanl i) δ hδpos hδle hδlim)
  calc
    _ ≤ ∑ i, ((∫ x, f x * Real.log (f x) ∂(Measure.pi μ)) -
        ∫ x, mean i x * Real.log (mean i x) ∂(Measure.pi μ)) :=
      le_of_tendsto_of_tendsto' (hT.sub hM) hR hpoint
    _ = _ := Finset.sum_congr rfl fun i _ =>
      (integral_entropy_update_eq_sub_integral_mul_log_mean μ i hfm hf hint hlog).symm

end Product
end NLAlib
