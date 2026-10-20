import NLAlib.Probability.Concentration.Entropy.RandomGradientEntropy
import NLAlib.ForMathlib.Probability.IndependentCopySwaps
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Two orientations of an actual independent-copy random proxy

For a bounded observable, the negative exponential entropy is oriented by
swapping only the coordinate of its individual summand. The common proxy is
used after this orientation and the finite sum. It needs no swap invariance.
This is an entropy prerequisite for independent-sum spectral universality.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]

omit [DecidableEq ι] [∀ i, IsProbabilityMeasure (ν i)] in
private theorem integrable_exp_mul_proxy_of_abs_bound
    (f : (ι → Ω) → ℝ) (hfm : Measurable f) {M : ℝ}
    (hbound : ∀ x, |f x| ≤ M)
    (W : ((ι → Ω) × (ι → Ω)) → ℝ)
    (hWi : Integrable W ((Measure.pi ν).prod (Measure.pi ν))) (s : ℝ) :
    Integrable (fun q => Real.exp (s * f q.1) * W q)
      ((Measure.pi ν).prod (Measure.pi ν)) := by
  apply hWi.bdd_mul (by
    have hm : Measurable (fun q : (ι → Ω) × (ι → Ω) => Real.exp (s * f q.1)) := by
      fun_prop
    exact hm.aestronglyMeasurable) (c := Real.exp (|s| * M))
  exact ae_of_all _ fun q => by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_mul_le_exp_abs_mul_of_abs_le (s := s) (hbound q.1)

/-- Positive exponential entropy is controlled by the actual random proxy.
The gradient comparison need only hold almost everywhere on the actual
joint law of the original and independent-copy product samples. -/
theorem entropy_exp_mul_pi_le_integral_proxy_of_bounded
    (f : (ι → Ω) → ℝ) (hfm : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M)
    (W : ((ι → Ω) × (ι → Ω)) → ℝ)
    (hWi : Integrable W ((Measure.pi ν).prod (Measure.pi ν)))
    (hgrad : ∀ᵐ q ∂((Measure.pi ν).prod (Measure.pi ν)),
      (∑ i, max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2) ≤ W q)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, s * f x * Real.exp (s * f x) ∂Measure.pi ν) -
      (∫ x, Real.exp (s * f x) ∂Measure.pi ν) *
        Real.log (∫ x, Real.exp (s * f x) ∂Measure.pi ν) ≤
      s ^ 2 * ∫ q : (ι → Ω) × (ι → Ω), Real.exp (s * f q.1) * W q
        ∂((Measure.pi ν).prod (Measure.pi ν)) := by
  have hUi (i : ι) : Integrable (fun q : (ι → Ω) × (ι → Ω) =>
      Real.exp (s * f q.1) * max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2)
      ((Measure.pi ν).prod (Measure.pi ν)) :=
    integrable_exp_mul_posPart_sub_sq_of_abs_le
      (fun q : (ι → Ω) × (ι → Ω) => f q.1)
      (fun q : (ι → Ω) × (ι → Ω) => f (Function.update q.1 i (q.2 i)))
      (by fun_prop) (by fun_prop) hM (fun q => hbound q.1) (fun q => hbound _) s
  have hU : Integrable (fun q : (ι → Ω) × (ι → Ω) =>
      Real.exp (s * f q.1) * ∑ i,
        max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2)
      ((Measure.pi ν).prod (Measure.pi ν)) := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i _ => hUi i)
  have h := integral_mono_ae hU
    (integrable_exp_mul_proxy_of_abs_bound ν f hfm hbound W hWi s)
    (hgrad.mono fun q hq => mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le)
  exact (entropy_exp_mul_pi_le_integral_resampling_posPart_sq_of_bounded
    ν f hfm M hM hbound hs).trans (mul_le_mul_of_nonneg_left h (sq_nonneg s))

/-- Orienting each coordinate replacement gives the actual negative
exponential entropy bound. The cost is `exp(s*b)` for increments bounded by
`b`; the proxy itself is never swapped or required to be invariant. -/
theorem entropy_exp_neg_mul_pi_le_exp_mul_integral_proxy_of_bounded
    (f : (ι → Ω) → ℝ) (hfm : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M)
    (W : ((ι → Ω) × (ι → Ω)) → ℝ)
    (hWi : Integrable W ((Measure.pi ν).prod (Measure.pi ν)))
    (hgrad : ∀ᵐ q ∂((Measure.pi ν).prod (Measure.pi ν)),
      (∑ i, max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2) ≤ W q)
    {b : ℝ}
    (hdiff : ∀ i, ∀ᵐ q ∂((Measure.pi ν).prod (Measure.pi ν)),
      |f q.1 - f (Function.update q.1 i (q.2 i))| ≤ b)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, s * (-f x) * Real.exp (s * (-f x)) ∂Measure.pi ν) -
      (∫ x, Real.exp (s * (-f x)) ∂Measure.pi ν) *
        Real.log (∫ x, Real.exp (s * (-f x)) ∂Measure.pi ν) ≤
      (Real.exp (s * b) * s ^ 2) *
        ∫ q : (ι → Ω) × (ι → Ω), Real.exp (s * (-f q.1)) * W q
          ∂((Measure.pi ν).prod (Measure.pi ν)) := by
  let μ := Measure.pi ν
  let P : ι → ((ι → Ω) × (ι → Ω)) → ℝ := fun i q =>
    Real.exp (s * (-f q.1)) * max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2
  let N : ι → ((ι → Ω) × (ι → Ω)) → ℝ := fun i q =>
    Real.exp (s * (-f q.1)) * max ((-f q.1) - (-f (Function.update q.1 i (q.2 i)))) 0 ^ 2
  have hN (i : ι) : Integrable (N i) (μ.prod μ) :=
    integrable_exp_mul_posPart_sub_sq_of_abs_le
      (fun q : (ι → Ω) × (ι → Ω) => -f q.1)
      (fun q : (ι → Ω) × (ι → Ω) => -f (Function.update q.1 i (q.2 i)))
      (by fun_prop) (by fun_prop) hM
      (fun q => by simpa only [abs_neg] using hbound q.1)
      (fun q => by simpa only [abs_neg] using hbound _) s
  have hP (i : ι) : Integrable (P i) (μ.prod μ) := by
    have hi : Integrable (fun q : (ι → Ω) × (ι → Ω) =>
        max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2) (μ.prod μ) := by
      apply Integrable.of_bound (by fun_prop) ((2 * M) ^ 2)
      exact ae_of_all _ fun q => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply (sq_le_sq₀ (le_max_right _ _) (by positivity)).mpr
        apply max_le _ (by positivity)
        linarith [(abs_le.mp (hbound q.1)).2, (abs_le.mp (hbound
          (Function.update q.1 i (q.2 i)))).1]
    apply hi.bdd_mul (by
      have hm : Measurable (fun q : (ι → Ω) × (ι → Ω) => Real.exp (s * (-f q.1))) := by
        fun_prop
      exact hm.aestronglyMeasurable) (c := Real.exp (|s| * M))
    exact ae_of_all _ fun q => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        Real.exp_mul_le_exp_abs_mul_of_abs_le (s := s)
          (by simpa only [abs_neg] using hbound q.1)
  have horient (i : ι) : (∫ q, N i q ∂μ.prod μ) ≤
      Real.exp (s * b) * ∫ q, P i q ∂μ.prod μ := by
    have hp := measurePreserving_prod_pi_update_swap ν i
    have hNi := hp.integrable_comp_of_integrable (hN i)
    have he := integral_prod_pi_update_swap ν i (N i) (hN i).aestronglyMeasurable
    rw [← he]
    have hmono := integral_mono_ae hNi ((hP i).const_mul (Real.exp (s * b))) ?_
    · simpa only [μ, Function.comp_def, integral_const_mul] using hmono
    filter_upwards [hdiff i] with q hq
    simp only [Function.comp_def, N, Function.update_self, Function.update_idem,
      Function.update_eq_self, neg_sub_neg]
    have hx : Real.exp (s * (-f (Function.update q.1 i (q.2 i)))) ≤
        Real.exp (s * b) * Real.exp (s * (-f q.1)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hd := (le_abs_self (f q.1 - f (Function.update q.1 i (q.2 i)))).trans hq
      nlinarith
    simpa only [P, mul_assoc] using mul_le_mul_of_nonneg_right hx
      (sq_nonneg (max (f q.1 - f (Function.update q.1 i (q.2 i))) 0))
  have hsum : (∫ q, ∑ i, N i q ∂μ.prod μ) ≤
      Real.exp (s * b) * ∫ q, ∑ i, P i q ∂μ.prod μ := by
    rw [integral_finsetSum Finset.univ (fun i _ => hN i),
      integral_finsetSum Finset.univ (fun i _ => hP i), Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => horient i
  have hproxy := integral_mono_ae
    (integrable_finsetSum Finset.univ (fun i _ => hP i))
    (integrable_exp_mul_proxy_of_abs_bound ν (fun x => -f x) (by fun_prop)
      (fun x => by simpa only [abs_neg] using hbound x) W hWi s) ?_
  · have hbase := entropy_exp_mul_pi_le_integral_resampling_posPart_sq_of_bounded
      ν (fun x => -f x) (by fun_prop) M hM
      (fun x => by simpa only [abs_neg] using hbound x) hs
    have he : (fun q : (ι → Ω) × (ι → Ω) =>
        Real.exp (s * (-f q.1)) * ∑ i,
          max ((-f q.1) - (-f (Function.update q.1 i (q.2 i)))) 0 ^ 2) =
        (fun q => ∑ i, N i q) := by
      ext q
      simp only [N, Finset.mul_sum]
    rw [he] at hbase
    have hall := hsum.trans (mul_le_mul_of_nonneg_left hproxy (Real.exp_pos _).le)
    exact hbase.trans ((mul_le_mul_of_nonneg_left hall (sq_nonneg s)).trans_eq (by ring))
  filter_upwards [hgrad] with q hq
  simpa only [P, ← Finset.mul_sum] using
    mul_le_mul_of_nonneg_left hq (Real.exp_pos (s * (-f q.1))).le

/-- Either exponential orientation is bounded by three times the same
actual random proxy when `s*b≤1`. Only the individual negative replacement
terms are swapped; no invariance property of `W` is assumed. -/
theorem entropy_exp_sign_mul_pi_le_three_integral_proxy_of_bounded
    (f : (ι → Ω) → ℝ) (hfm : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M)
    (W : ((ι → Ω) × (ι → Ω)) → ℝ)
    (hWi : Integrable W ((Measure.pi ν).prod (Measure.pi ν)))
    (hgrad : ∀ᵐ q ∂((Measure.pi ν).prod (Measure.pi ν)),
      (∑ i, max (f q.1 - f (Function.update q.1 i (q.2 i))) 0 ^ 2) ≤ W q)
    {b : ℝ}
    (hdiff : ∀ i, ∀ᵐ q ∂((Measure.pi ν).prod (Measure.pi ν)),
      |f q.1 - f (Function.update q.1 i (q.2 i))| ≤ b)
    {s : ℝ} (hs : 0 ≤ s) (hsb : s * b ≤ 1)
    {e : ℝ} (he : e = 1 ∨ e = -1) :
    (∫ x, s * (e * f x) * Real.exp (s * (e * f x)) ∂Measure.pi ν) -
      (∫ x, Real.exp (s * (e * f x)) ∂Measure.pi ν) *
        Real.log (∫ x, Real.exp (s * (e * f x)) ∂Measure.pi ν) ≤
      (3 * s ^ 2) * ∫ q : (ι → Ω) × (ι → Ω),
        Real.exp (s * (e * f q.1)) * W q
          ∂((Measure.pi ν).prod (Measure.pi ν)) := by
  have hW0 : ∀ᵐ q ∂((Measure.pi ν).prod (Measure.pi ν)), 0 ≤ W q :=
    hgrad.mono fun q hq => (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans hq
  have hnonneg (u : ℝ) : 0 ≤ ∫ q : (ι → Ω) × (ι → Ω),
      Real.exp (u * f q.1) * W q ∂((Measure.pi ν).prod (Measure.pi ν)) :=
    integral_nonneg_of_ae (hW0.mono fun q hq => mul_nonneg (Real.exp_pos _).le hq)
  rcases he with rfl | rfl
  · simpa only [one_mul] using
      (entropy_exp_mul_pi_le_integral_proxy_of_bounded ν f hfm M hM hbound W hWi
        hgrad hs).trans (by nlinarith [hnonneg s, sq_nonneg s])
  · have h := entropy_exp_neg_mul_pi_le_exp_mul_integral_proxy_of_bounded
      ν f hfm M hM hbound W hWi hgrad hdiff hs
    have hE : Real.exp (s * b) ≤ 3 :=
      (Real.exp_le_exp.mpr hsb).trans (Real.exp_one_lt_three).le
    have hN : 0 ≤ ∫ q : (ι → Ω) × (ι → Ω),
        Real.exp (s * (-f q.1)) * W q ∂((Measure.pi ν).prod (Measure.pi ν)) := by
      simpa only [neg_mul, mul_neg] using hnonneg (-s)
    simpa only [neg_one_mul] using h.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE (sq_nonneg s)) hN)

end NLAlib
