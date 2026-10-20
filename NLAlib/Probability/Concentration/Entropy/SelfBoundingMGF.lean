import NLAlib.ForMathlib.Analysis.Calculus.LogarithmicDifferentialBounds
import NLAlib.Probability.Concentration.Entropy.RandomGradientEntropy
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Exponential moments from bounded coordinate deletion differences

Actual product-law entropy and native MGF derivatives prove a coefficient-one
self-bounding estimate. Its radius is weaker than literal source equation(5.1),
but preserves the source scale for universal-constant concentration results.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace NLAlib

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]

omit [MeasurableSpace Ω] in
/-- Deletion lower bounds yield the actual independent-copy positive-gradient
bound. No measurability of the auxiliary deletion functions is needed, since
only their pointwise comparison and coordinate independence are used. -/
theorem sum_resampling_posPart_sq_le_of_deletions
    (W : (ι → Ω) → ℝ) (Wi : ι → (ι → Ω) → ℝ)
    (hlower : ∀ i x, Wi i x ≤ W x)
    (hindep : ∀ i x t, Wi i (Function.update x i t) = Wi i x)
    {a : ℝ} (hsum : ∀ x, ∑ i, (W x - Wi i x) ^ 2 ≤ a * W x)
    (x y : ι → Ω) :
    ∑ i, max (W x - W (Function.update x i (y i))) 0 ^ 2 ≤ a * W x := by
  apply le_trans _ (hsum x)
  apply Finset.sum_le_sum
  intro i _
  apply (sq_le_sq₀ (le_max_right _ _) (sub_nonneg.mpr (hlower i x))).mpr
  apply max_le _ (sub_nonneg.mpr (hlower i x))
  have h := hlower i (Function.update x i (y i))
  rw [hindep] at h
  linarith

/-- Actual self-bounding exponential entropy from coordinate deletions.
Boundedness proves every displayed integrability statement; the entropy
inequality is derived from the actual product law. -/
theorem entropy_exp_mul_pi_le_of_bounded_deletions
    (W : (ι → Ω) → ℝ) (hWm : Measurable W) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |W x| ≤ M) (Wi : ι → (ι → Ω) → ℝ)
    (hlower : ∀ i x, Wi i x ≤ W x)
    (hindep : ∀ i x t, Wi i (Function.update x i t) = Wi i x)
    {a : ℝ} (hsum : ∀ x, ∑ i, (W x - Wi i x) ^ 2 ≤ a * W x)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, s * W x * Real.exp (s * W x) ∂Measure.pi ν) -
      (∫ x, Real.exp (s * W x) ∂Measure.pi ν) *
        Real.log (∫ x, Real.exp (s * W x) ∂Measure.pi ν) ≤
      a * s ^ 2 * ∫ x, W x * Real.exp (s * W x) ∂Measure.pi ν := by
  let μ := Measure.pi ν
  have hY : Integrable (fun x => Real.exp (s * W x)) μ := by
    apply Integrable.of_bound (by fun_prop) (Real.exp (|s| * M))
    exact ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        Real.exp_mul_le_exp_abs_mul_of_abs_le (s := s) (hbound x)
  have hWY : Integrable (fun x => W x * Real.exp (s * W x)) μ :=
    hY.bdd_mul hWm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hUi (i : ι) : Integrable (fun q : (ι → Ω) × (ι → Ω) =>
      Real.exp (s * W q.1) * max (W q.1 - W (Function.update q.1 i (q.2 i))) 0 ^ 2)
      (μ.prod μ) :=
    integrable_exp_mul_posPart_sub_sq_of_abs_le
      (fun q : (ι → Ω) × (ι → Ω) => W q.1)
      (fun q : (ι → Ω) × (ι → Ω) => W (Function.update q.1 i (q.2 i)))
      (by fun_prop) (by fun_prop) hM (fun q => hbound q.1) (fun q => hbound _) s
  have hU : Integrable (fun q : (ι → Ω) × (ι → Ω) =>
      Real.exp (s * W q.1) * ∑ i,
        max (W q.1 - W (Function.update q.1 i (q.2 i))) 0 ^ 2) (μ.prod μ) := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i _ => hUi i)
  have hpoint (q : (ι → Ω) × (ι → Ω)) :
      Real.exp (s * W q.1) * (∑ i,
        max (W q.1 - W (Function.update q.1 i (q.2 i))) 0 ^ 2) ≤
      a * (W q.1 * Real.exp (s * W q.1)) := by
    have h := mul_le_mul_of_nonneg_left
      (sum_resampling_posPart_sq_le_of_deletions W Wi hlower hindep hsum q.1 q.2)
      (Real.exp_pos (s * W q.1)).le
    nlinarith
  have hmono := integral_mono hU ((hWY.const_mul a).comp_fst μ) hpoint
  rw [integral_fun_fst (fun x : ι → Ω => a * (W x * Real.exp (s * W x))),
    probReal_univ, one_smul, integral_const_mul] at hmono
  have h := entropy_exp_mul_pi_le_integral_resampling_posPart_sq_of_bounded
    ν W hWm M hM hbound hs
  exact h.trans ((mul_le_mul_of_nonneg_left hmono (sq_nonneg s)).trans_eq (by ring))

/-- A genuine MGF bound from bounded coordinate deletions. The radius is
`a*s<1` and the statement includes `a=0`, `s=0`, and an empty index family.
This is a weaker-constant form of the self-bounding MGF step used in source
arXiv:2201.05142v3, Proposition5.6, and does not claim literal equation(5.1). -/
theorem log_integral_exp_mul_pi_le_of_bounded_deletions
    (W : (ι → Ω) → ℝ) (hWm : Measurable W) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |W x| ≤ M) (Wi : ι → (ι → Ω) → ℝ)
    (hlower : ∀ i x, Wi i x ≤ W x)
    (hindep : ∀ i x t, Wi i (Function.update x i t) = Wi i x)
    {a : ℝ} (ha : 0 ≤ a) (hsum : ∀ x, ∑ i, (W x - Wi i x) ^ 2 ≤ a * W x)
    {s : ℝ} (hs : 0 ≤ s) (hdom : a * s < 1) :
    Real.log (∫ x, Real.exp (s * W x) ∂Measure.pi ν) ≤
      s * (∫ x, W x ∂Measure.pi ν) / (1 - a * s) := by
  let μ := Measure.pi ν
  have hint (u : ℝ) : Integrable (fun x => Real.exp (u * W x)) μ := by
    apply Integrable.of_bound (by fun_prop) (Real.exp (|u| * M))
    exact ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        Real.exp_mul_le_exp_abs_mul_of_abs_le (s := u) (hbound x)
  have hint' (u : ℝ) : u ∈ interior (integrableExpSet W μ) := by
    have he : integrableExpSet W μ = Set.univ := Set.eq_univ_of_forall hint
    simp [he]
  have hderiv (u : ℝ) : HasDerivAt (cgf W μ) (deriv (cgf W μ) u) u :=
    (analyticAt_cgf (hint' u)).differentiableAt.hasDerivAt
  have hde (u : ℝ) (hu : 0 < u) (_hdom : a * u < 1) :
      u * deriv (cgf W μ) u - cgf W μ u ≤ a * u ^ 2 * deriv (cgf W μ) u := by
    have h := entropy_exp_mul_pi_le_of_bounded_deletions ν W hWm M hM hbound
      Wi hlower hindep hsum hu.le
    have he : (∫ x, u * W x * Real.exp (u * W x) ∂μ) =
        u * ∫ x, W x * Real.exp (u * W x) ∂μ := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    change (∫ x, u * W x * Real.exp (u * W x) ∂μ) -
      mgf W μ u * cgf W μ u ≤ _ at h
    rw [he] at h
    have hpos := mgf_pos (hint u)
    have hh := div_le_div_of_nonneg_right h hpos.le
    rw [deriv_cgf (hint' u)]
    calc u * ((∫ x, W x * Real.exp (u * W x) ∂μ) / mgf W μ u) - cgf W μ u =
        (u * (∫ x, W x * Real.exp (u * W x) ∂μ) - mgf W μ u * cgf W μ u) / mgf W μ u := by
          field_simp [hpos.ne']
      _ ≤ (a * u ^ 2 * (∫ x, W x * Real.exp (u * W x) ∂μ)) / mgf W μ u := hh
      _ = a * u ^ 2 * ((∫ x, W x * Real.exp (u * W x) ∂μ) / mgf W μ u) := by ring
  have h := Real.le_div_one_sub_mul_of_hasDerivAt_self_bound
    (cgf W μ) (deriv (cgf W μ)) hderiv (by simp) ha hde hs hdom
  rw [deriv_cgf_zero (hint' 0), probReal_univ, div_one] at h
  exact h

/-- An explicit weaker-radius substitute for source equation(5.1).
Only the exact bounded-deletion assumptions above are used. -/
theorem log_integral_exp_div_two_mul_pi_le_of_bounded_deletions
    (W : (ι → Ω) → ℝ) (hWm : Measurable W) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |W x| ≤ M) (Wi : ι → (ι → Ω) → ℝ)
    (hlower : ∀ i x, Wi i x ≤ W x)
    (hindep : ∀ i x t, Wi i (Function.update x i t) = Wi i x)
    {a : ℝ} (ha : 0 < a) (hsum : ∀ x, ∑ i, (W x - Wi i x) ^ 2 ≤ a * W x) :
    Real.log (∫ x, Real.exp (W x / (2 * a)) ∂Measure.pi ν) ≤
      (∫ x, W x ∂Measure.pi ν) / a := by
  have hs : 0 ≤ (2 * a)⁻¹ := inv_nonneg.mpr (by positivity)
  have hdom : a * (2 * a)⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have h := log_integral_exp_mul_pi_le_of_bounded_deletions ν W hWm M hM hbound
    Wi hlower hindep ha.le hsum hs hdom
  have hexp : (fun x => Real.exp ((2 * a)⁻¹ * W x)) =
      (fun x => Real.exp (W x / (2 * a))) := by
    ext x
    congr 1
    ring
  rw [hexp] at h
  convert h using 1
  field_simp [ha.ne']
  norm_num

end Product

/-- A variable-coefficient Herbst argument from actual native MGF derivatives.
The exponential integrability assumption concerns finiteness only, and the
entropy hypothesis is integrated here rather than assuming the desired MGF
bound. In bounded-observable applications all finiteness is automatic. -/
theorem integral_exp_mul_le_exp_of_rational_entropy_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) {c C : ℝ} (hc : 0 ≤ c)
    (hint : ∀ u : ℝ, Integrable (fun x => Real.exp (u * f x)) μ)
    (hent : ∀ u : ℝ, 0 < u → c * u < 1 →
      (∫ x, u * f x * Real.exp (u * f x) ∂μ) -
        (∫ x, Real.exp (u * f x) ∂μ) * Real.log (∫ x, Real.exp (u * f x) ∂μ) ≤
      (C * u ^ 2 / (1 - c * u) ^ 2) * ∫ x, Real.exp (u * f x) ∂μ)
    {s : ℝ} (hs : 0 ≤ s) (hdom : c * s < 1) :
    (∫ x, Real.exp (s * f x) ∂μ) ≤
      Real.exp (s * (∫ x, f x ∂μ) + C * s ^ 2 / (1 - c * s)) := by
  have hint' (u : ℝ) : u ∈ interior (integrableExpSet f μ) := by
    have he : integrableExpSet f μ = Set.univ := Set.eq_univ_of_forall hint
    simp [he]
  have hderiv (u : ℝ) : HasDerivAt (cgf f μ) (deriv (cgf f μ) u) u :=
    (analyticAt_cgf (hint' u)).differentiableAt.hasDerivAt
  have hde (u : ℝ) (hu : 0 < u) (hcu : c * u < 1) :
      u * deriv (cgf f μ) u - cgf f μ u ≤ C * u ^ 2 / (1 - c * u) ^ 2 := by
    have he := hent u hu hcu
    have hfe : (∫ x, u * f x * Real.exp (u * f x) ∂μ) =
        u * ∫ x, f x * Real.exp (u * f x) ∂μ := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    change (∫ x, u * f x * Real.exp (u * f x) ∂μ) -
      mgf f μ u * cgf f μ u ≤ _ at he
    rw [hfe] at he
    have hpos := mgf_pos (hint u)
    have hh := div_le_div_of_nonneg_right he hpos.le
    rw [deriv_cgf (hint' u)]
    calc u * ((∫ x, f x * Real.exp (u * f x) ∂μ) / mgf f μ u) - cgf f μ u =
        (u * (∫ x, f x * Real.exp (u * f x) ∂μ) - mgf f μ u * cgf f μ u) / mgf f μ u := by
          field_simp [hpos.ne']
      _ ≤ ((C * u ^ 2 / (1 - c * u) ^ 2) * mgf f μ u) / mgf f μ u := hh
      _ = C * u ^ 2 / (1 - c * u) ^ 2 := by rw [mul_div_cancel_right₀ _ hpos.ne']
  have h := Real.le_affine_add_div_of_hasDerivAt_bound
    (cgf f μ) (deriv (cgf f μ)) hderiv (by simp) hc hde hs hdom
  rw [deriv_cgf_zero (hint' 0), probReal_univ, div_one] at h
  calc (∫ x, Real.exp (s * f x) ∂μ) = Real.exp (cgf f μ s) :=
      (Real.exp_log (mgf_pos (hint s))).symm
    _ ≤ _ := Real.exp_le_exp.mpr h

end NLAlib
