import NLAlib.Probability.Concentration.Matrix.IndependentResolventTail
import NLAlib.Probability.Concentration.Matrix.ResolventVarianceProxyExpectation
import NLAlib.Probability.Concentration.Basic.SubGammaMoments
import NLAlib.Probability.Transforms.ResolventNormMoments

/-!
# Actual independent-sum resolvent Lp moments

The genuine two-sign exponential bound controls actual even Lp fluctuations.
Replacing the constructed copy-proxy expectation by its proved estimate gives
a deterministic bound in the original matrix variance and bilinear geometry.
Source: arXiv:2201.05142v3, Proposition 5.6 and Lemma 7.5.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib

variable {ι n Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [MeasurableSpace Ω]

open scoped Matrix.Norms.L2Operator in
/-- The actual centered resolvent of bounded independent Hermitian increments
has even Lp norm controlled by its constructed independent-copy proxy.
Zero radius, empty increments and empty matrix shapes are included. -/
theorem lpNorm_centered_specNorm_resolvent_pi_le_sqrt_proxy_expectation
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (A₀ : Matrix n n ℂ) (hA₀ : A₀.IsHermitian)
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R : ℝ} (hR : 0 ≤ R)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    let E := ∫ q : (ι → Ω) × (ι → Ω),
      resolventVarianceProxy (fun i => Z i (q.1 i)-Z i (q.2 i)) Finset.univ R |ζ.im|
        ∂((Measure.pi ν).prod (Measure.pi ν))
    lpNorm (fun x : ι → Ω => specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ) -
      ∫ y : ι → Ω, specNorm (resolvent (A₀ + ∑ i, Z i (y i)) ζ) ∂Measure.pi ν)
        ((2*p : ℕ) : ℝ≥0∞) (Measure.pi ν) ≤
      4*Real.sqrt (12*E*p) +
        8*Real.sqrt (6*(16*R^2/|ζ.im|^4+64*R^4/|ζ.im|^6))*p := by
  let E := ∫ q : (ι → Ω) × (ι → Ω),
    resolventVarianceProxy (fun i => Z i (q.1 i)-Z i (q.2 i)) Finset.univ R |ζ.im|
      ∂((Measure.pi ν).prod (Measure.pi ν))
  let c := Real.sqrt (6*(16*R^2/|ζ.im|^4+64*R^4/|ζ.im|^6))
  have hE : 0 ≤ E := integral_nonneg fun _ =>
    matrixVarianceProxy_nonneg _ _ (by positivity) (by positivity)
  have hXm : Measurable (fun x : ι → Ω => A₀ + ∑ i, Z i (x i)) := by
    exact measurable_const.add (Finset.measurable_sum Finset.univ
      (fun i _ => (hZm i).comp (measurable_pi_apply i)))
  have hXH : ∀ᵐ x : ι → Ω ∂Measure.pi ν, (A₀ + ∑ i, Z i (x i)).IsHermitian := by
    have hh : ∀ᵐ x : ι → Ω ∂Measure.pi ν, ∀ i, (Z i (x i)).IsHermitian :=
      ae_all_iff.mpr fun i => (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hZH i)
    exact hh.mono fun x hx => hA₀.add (isSelfAdjoint_sum _ fun i _ => hx i)
  have hmem := memLp_specNorm_resolvent (Measure.pi ν) _ hXm.aemeasurable hXH hζ
    ((2*p : ℕ) : ℝ≥0∞)
  apply lpNorm_two_mul_le_sqrt_add_of_subgamma_mgf hp
    (hmem.sub (memLp_const _)) (mul_nonneg (by norm_num) hE) (Real.sqrt_nonneg _)
  · intro s _ _ e _
    exact integrable_exp_sign_mul_centered_specNorm_resolvent_pi ν A₀ hA₀ Z hZm hZH ζ hζ s e
  · intro s hs hdom e he
    have h := integral_exp_sign_mul_centered_specNorm_resolvent_pi_le
      ν A₀ hA₀ Z hZm hR hZH hZ ζ hζ hs hdom he
    apply h.trans_eq
    congr 1
    dsimp only [E, c]
    field_simp
    ring

open scoped Matrix.Norms.L2Operator in
/-- Actual non-Gaussian resolvent Lp norms are controlled by their actual
means and a derived bilinear/variance expression. No MGF, moment or proxy
estimate is supplied as an assumption.
atlas: independent-sum-spectrum-universality (partial) -/
theorem lpNorm_specNorm_resolvent_pi_le_integral_add_of_bilinear_moments
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (A₀ : Matrix n n ℂ) (hA₀ : A₀.IsHermitian)
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R v : ℝ} (hR : 0 ≤ R)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i = 0)
    (hvariance : ∀ a b : EuclideanSpace ℂ n, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      (∑ i, ∫ ω, ‖star a.ofLp ⬝ᵥ (Z i ω *ᵥ b.ofLp)‖ ^ 2 ∂ν i) ≤ v)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    let B := (2/|ζ.im|^4)*(8*v+64*R*
      ∫ x : ι → Ω, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν) +
      (32*R^2/|ζ.im|^6)*((Real.exp 1-1)*specNorm (∑ i, ∫ ω, Z i ω^2 ∂ν i)+
        R^2*Real.log (Fintype.card n))
    lpNorm (fun x : ι → Ω => specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ))
      ((2*p : ℕ) : ℝ≥0∞) (Measure.pi ν) ≤
        (∫ x : ι → Ω, specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ) ∂Measure.pi ν) +
          4*Real.sqrt (12*B*p) +
            8*Real.sqrt (6*(16*R^2/|ζ.im|^4+64*R^4/|ζ.im|^6))*p := by
  let f (x : ι → Ω) := specNorm (resolvent (A₀ + ∑ i, Z i (x i)) ζ)
  let m := ∫ x : ι → Ω, f x ∂Measure.pi ν
  let B := (2/|ζ.im|^4)*(8*v+64*R*
    ∫ x : ι → Ω, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν) +
    (32*R^2/|ζ.im|^6)*((Real.exp 1-1)*specNorm (∑ i, ∫ ω, Z i ω^2 ∂ν i)+
      R^2*Real.log (Fintype.card n))
  let E := ∫ q : (ι → Ω) × (ι → Ω),
    resolventVarianceProxy (fun i => Z i (q.1 i)-Z i (q.2 i)) Finset.univ R |ζ.im|
      ∂((Measure.pi ν).prod (Measure.pi ν))
  have hEB : E ≤ B := (integrable_and_integral_resolventVarianceProxy_copy_pi_le
    ν Z hZm hR (abs_pos.mpr hζ) hZH hZ hmean hvariance).2
  have hfl := lpNorm_centered_specNorm_resolvent_pi_le_sqrt_proxy_expectation
    ν A₀ hA₀ Z hZm hR hZH hZ ζ hζ hp
  have hs : Real.sqrt (12*E*p) ≤ Real.sqrt (12*B*p) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEB (by norm_num)) (Nat.cast_nonneg p))
  have hm : 0 ≤ m := integral_nonneg fun _ => specNorm_nonneg _
  have he : f = (fun _ : ι → Ω => m)+(fun x => f x-m) := by ext x; simp
  change lpNorm f ((2*p : ℕ) : ℝ≥0∞) (Measure.pi ν) ≤ m +
    4*Real.sqrt (12*B*p) + 8*Real.sqrt (6*(16*R^2/|ζ.im|^4+64*R^4/|ζ.im|^6))*p
  calc
    _ ≤ lpNorm (fun _ : ι → Ω => m) ((2*p : ℕ) : ℝ≥0∞) (Measure.pi ν) +
        lpNorm (fun x => f x-m) ((2*p : ℕ) : ℝ≥0∞) (Measure.pi ν) := by
      conv_lhs => rw [he]
      apply lpNorm_add_le (memLp_const _)
      exact_mod_cast (by omega : 1 ≤ 2*p)
    _ = m + lpNorm (fun x => f x-m) ((2*p : ℕ) : ℝ≥0∞) (Measure.pi ν) := by
      rw [lpNorm_const' (by positivity) (by finiteness), probReal_univ, Real.one_rpow,
        mul_one, Real.norm_eq_abs, abs_of_nonneg hm]
    _ ≤ _ := by
      have hroot := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4)
      have hadd := add_le_add hroot (le_refl
        (8*Real.sqrt (6*(16*R^2/|ζ.im|^4+64*R^4/|ζ.im|^6))*p))
      simpa only [add_assoc] using add_le_add (le_refl m) (hfl.trans hadd)

end NLAlib
