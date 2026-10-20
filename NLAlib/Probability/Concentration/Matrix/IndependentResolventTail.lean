import NLAlib.Probability.Concentration.Matrix.IndependentResolventMGF
import NLAlib.ForMathlib.Probability.SubGammaOptimization

/-!
# Actual two-sided resolvent-norm concentration with a random proxy

The observable is the genuine resolvent of an independent Hermitian matrix
sum with arbitrary deterministic Hermitian offset. Its random proxy, gradient
and signed exponential moments have already been constructed and proved.
These are concentration prerequisites for independent-sum spectral universality;
the expectation bound for this proxy and the spectral conclusion are separate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace NLAlib

variable {ι n Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    [MeasurableSpace Ω]

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- Every real signed exponential of the actual centered resolvent norm is
integrable. Hermitian marginal support, nonreal spectral parameter and the
native resolvent bound suffice; no bounded-summand premise is needed. -/
theorem integrable_exp_sign_mul_centered_specNorm_resolvent_pi
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (A₀ : Matrix n n ℂ) (hA₀ : A₀.IsHermitian)
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (s e : ℝ) :
    Integrable (fun x : ι → Ω => Real.exp (s * (e *
      (specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ) -
        ∫ y : ι → Ω, specNorm (resolvent (A₀ + ∑ i, Z i (y i)) ζ) ∂Measure.pi ν))))
      (Measure.pi ν) := by
  let : SecondCountableTopology (Matrix n n ℂ) :=
    inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  let μ := Measure.pi ν
  let X : (ι → Ω) → Matrix n n ℂ := fun x => A₀ + ∑ i, Z i (x i)
  let f : (ι → Ω) → ℝ := fun x => specNorm (resolvent (X x) ζ)
  have hXm : Measurable X := by dsimp [X]; fun_prop
  have hfm : Measurable f := by
    dsimp only [f]
    simpa only [specNorm_eq_norm, Function.comp_def] using
      ((measurable_matrix_resolvent ζ).comp hXm).norm
  have hgood : ∀ᵐ x ∂μ, ∀ i, (Z i (x i)).IsHermitian :=
    ae_all_iff.mpr fun i => (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hZH i)
  have hbound : ∀ᵐ x ∂μ, |f x| ≤ |ζ.im|⁻¹ := by
    filter_upwards [hgood] with x hx
    have hH : (X x).IsHermitian := hA₀.add (isSelfAdjoint_sum _ (fun i _ => hx i))
    rw [abs_of_nonneg (specNorm_nonneg _)]
    exact hH.specNorm_resolvent_le hζ
  have hcb : ∀ᵐ x ∂μ, |e * (f x - ∫ y, f y ∂μ)| ≤
      |e| * (|ζ.im|⁻¹ + |∫ y, f y ∂μ|) := by
    filter_upwards [hbound] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((abs_sub (f x) (∫ y, f y ∂μ)).trans (add_le_add hx le_rfl)) (abs_nonneg e)
  exact integrable_exp_mul_of_mem_Icc ((hfm.sub measurable_const).const_mul e).aemeasurable
    (hcb.mono fun x hx => abs_le.mp hx)

private theorem resolvent_sign_subgamma_mgf
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (A₀ : Matrix n n ℂ) (hA₀ : A₀.IsHermitian)
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R : ℝ} (hR : 0 ≤ R)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZB : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (ζ : ℂ) (hζ : ζ.im ≠ 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hdom : Real.sqrt (6 * (16 * R ^ 2 / |ζ.im| ^ 4 + 64 * R ^ 4 / |ζ.im| ^ 6)) * s < 1)
    {e : ℝ} (he : e = 1 ∨ e = -1) :
    (∫ x : ι → Ω, Real.exp (s * (e *
      (specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ) -
        ∫ y : ι → Ω, specNorm (resolvent (A₀ + ∑ i, Z i (y i)) ζ) ∂Measure.pi ν)))
      ∂Measure.pi ν) ≤
      (1 : ℝ) * Real.exp ((12 * ∫ q : (ι → Ω) × (ι → Ω),
        resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R |ζ.im|
          ∂((Measure.pi ν).prod (Measure.pi ν))) * s ^ 2 /
        (2 * (1 - Real.sqrt (6 *
          (16 * R ^ 2 / |ζ.im| ^ 4 + 64 * R ^ 4 / |ζ.im| ^ 6)) * s))) := by
  have h := integral_exp_sign_mul_centered_specNorm_resolvent_pi_le
    ν A₀ hA₀ Z hZm hR hZH hZB ζ hζ hs hdom he
  apply h.trans_eq
  rw [one_mul]
  congr 1
  field_simp
  ring

/-- Strict two-sided concentration of the genuine resolvent norm around its
actual mean, with the literal original/copy variance-proxy expectation.
All nonnegative radii are included, including `R=0`, empty coordinates and
empty matrix dimension. In particular no proxy-expectation bound is assumed.
atlas: independent-sum-spectrum-universality (partial) -/
theorem measureReal_gt_abs_centered_specNorm_resolvent_pi_le
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (A₀ : Matrix n n ℂ) (hA₀ : A₀.IsHermitian)
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R : ℝ} (hR : 0 ≤ R)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZB : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi ν).real {x | Real.sqrt
      (24 * (∫ q : (ι → Ω) × (ι → Ω),
        resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R |ζ.im|
          ∂((Measure.pi ν).prod (Measure.pi ν))) * t) +
      Real.sqrt (6 * (16 * R ^ 2 / |ζ.im| ^ 4 + 64 * R ^ 4 / |ζ.im| ^ 6)) * t <
        |specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ) -
          ∫ y : ι → Ω, specNorm (resolvent (A₀ + ∑ i, Z i (y i)) ζ) ∂Measure.pi ν|} ≤
      2 * Real.exp (-t) := by
  let E := ∫ q : (ι → Ω) × (ι → Ω),
    resolventVarianceProxy (fun i => Z i (q.1 i) - Z i (q.2 i)) Finset.univ R |ζ.im|
      ∂((Measure.pi ν).prod (Measure.pi ν))
  have hE : 0 ≤ E := integral_nonneg fun _ =>
    matrixVarianceProxy_nonneg _ _ (by positivity) (by positivity)
  have h := measureReal_gt_abs_sub_sqrt_add_le_of_sign_subgamma_mgf
    (μ := Measure.pi ν)
    (X := fun x => specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ))
    (m := ∫ y : ι → Ω, specNorm (resolvent (A₀ + ∑ i, Z i (y i)) ζ) ∂Measure.pi ν)
    (d := 1) (V := 12 * E)
    (c := Real.sqrt (6 * (16 * R ^ 2 / |ζ.im| ^ 4 + 64 * R ^ 4 / |ζ.im| ^ 6)))
    (by norm_num) (by positivity) (Real.sqrt_nonneg _)
    (fun e _ s _ _ => integrable_exp_sign_mul_centered_specNorm_resolvent_pi
      ν A₀ hA₀ Z hZm hZH ζ hζ s e)
    (fun e he s hs hdom => resolvent_sign_subgamma_mgf
      ν A₀ hA₀ Z hZm hR hZH hZB ζ hζ hs hdom he) ht
  have hsqrt : Real.sqrt (2 * (12 * E) * t) = Real.sqrt (24 * E * t) := by
    congr 1
    ring
  simpa only [hsqrt, E, mul_one] using h

end NLAlib
