import NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesSupport
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-! # Positive Stieltjes families cannot cancel mass in an averaged gap

Cauchy regularization reconstructs a compact test for each actual finite
measure. Fubini and dominated convergence show that a vanishing averaged
imaginary part forces the test integral to vanish almost everywhere in
the parameter. No measurable measure-valued kernel is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace MeasureTheory

private theorem stieltjesFamily_regularization_bound
    (ρ : FiniteMeasure ℝ) (f : ℝ →ᵇ ℝ) (γ : NNReal) (hγ : γ≠0) :
    ‖∫ x : ℝ, f x*(∫ t : ℝ, cauchyPDFReal t γ x ∂(ρ : Measure ℝ))‖≤
      ‖f‖*(ρ.mass : ℝ) := by
  rw [integral_cauchyRegularization_eq (ρ : Measure ℝ) f γ hγ]
  have hinner (x : ℝ) : ‖∫ t : ℝ, f (x+γ*t) ∂cauchyMeasure 0 1‖≤‖f‖ := by
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := cauchyMeasure 0 1)
        (Eventually.of_forall fun t => f.norm_coe_le_norm (x+γ*t))
  have hh := norm_integral_le_of_norm_le_const (μ := (ρ : Measure ℝ))
    (Eventually.of_forall hinner)
  simpa only [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal] using hh

/-- For a genuine positive finite Stieltjes family, a locally uniform
O(height) bound on the averaged imaginary transform forces every fixed
nonnegative compact test in that region to have zero integral for
almost every parameter. The sample measures need not form an assumed
measurable kernel: measurability of the test integrals follows from
Cauchy regularization of the actual transforms. -/
theorem ae_integral_eq_zero_of_average_im_stieltjes_le_mul
    {T : Type*} [MeasurableSpace T] (ν : Measure T) [IsProbabilityMeasure ν]
    (ρ : T → FiniteMeasure ℝ) (r : T → ℂ → ℂ)
    (hrep : ∀ t : T, ∀ z : ℂ, 0<z.im → r t z=
      ∫ x : ℝ, ((x : ℂ)-z)⁻¹ ∂(ρ t : Measure ℝ))
    (B : NNReal) (hmass : ∀ᵐ t ∂ν, (ρ t).mass≤B)
    (hmeas : ∀ γ : NNReal, γ≠0 → AEStronglyMeasurable
      (fun p : T×ℝ => (r p.1 ((p.2 : ℂ)+(γ : ℝ)*Complex.I)).im) (ν.prod volume))
    (f : ℝ →ᵇ ℝ) (hfint : Integrable f) (hfnonneg : ∀ x, 0≤f x)
    (U : Set ℝ) (hfzero : ∀ x ∉ U, f x=0) (C : ℝ)
    (haverage : ∀ x ∈ U, ∀ γ : NNReal, γ≠0 →
      (∫ t : T, (r t ((x : ℂ)+(γ : ℝ)*Complex.I)).im ∂ν)≤C*(γ : ℝ)) :
    ∀ᵐ t ∂ν, ∫ x : ℝ, f x ∂(ρ t : Measure ℝ)=0 := by
  let k (γ : NNReal) (t : T) (x : ℝ) :=
    f x*(Real.pi⁻¹*(r t ((x : ℂ)+(γ : ℝ)*Complex.I)).im)
  let a (γ : NNReal) (t : T) := ∫ x : ℝ, k γ t x
  let g (t : T) := ∫ x : ℝ, f x ∂(ρ t : Measure ℝ)
  have hkeq (γ : NNReal) (hγ : γ≠0) (t : T) (x : ℝ) :
      k γ t x=f x*(∫ y : ℝ, cauchyPDFReal y γ x ∂(ρ t : Measure ℝ)) := by
    have hz : 0<((x : ℂ)+(γ : ℝ)*Complex.I).im := by
      simpa using (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ))
    rw [Complex.integral_cauchyPDFReal_eq_inv_pi_mul_im_integral (ρ t : Measure ℝ) x γ hγ,
      ← hrep t _ hz]
  have hknonneg (γ : NNReal) (hγ : γ≠0) (t : T) (x : ℝ) : 0≤k γ t x := by
    rw [hkeq γ hγ]
    exact mul_nonneg (hfnonneg x) (integral_nonneg fun y => (cauchyPDF_pos y hγ x).le)
  have hki (γ : NNReal) (hγ : γ≠0) (t : T) : Integrable (k γ t) := by
    have hi := (integrable_boundedContinuousFunction_mul_cauchyPDFReal_prod
      (ρ t : Measure ℝ) f γ hγ).integral_prod_right
    simp_rw [integral_const_mul] at hi
    change Integrable (fun x : ℝ => k γ t x)
    simpa only [hkeq γ hγ] using hi
  have hanorm (γ : NNReal) (hγ : γ≠0) (t : T) :
      ‖a γ t‖≤‖f‖*((ρ t).mass : ℝ) := by
    simpa only [a,hkeq γ hγ] using stieltjesFamily_regularization_bound (ρ t) f γ hγ
  have hkmeas (γ : NNReal) (hγ : γ≠0) :
      AEStronglyMeasurable (fun p : T×ℝ => k γ p.1 p.2) (ν.prod volume) := by
    exact (f.continuous.measurable.comp measurable_snd).aestronglyMeasurable.mul
      ((hmeas γ hγ).const_mul Real.pi⁻¹)
  have hkiprod (γ : NNReal) (hγ : γ≠0) :
      Integrable (fun p : T×ℝ => k γ p.1 p.2) (ν.prod volume) := by
    apply (integrable_prod_iff (hkmeas γ hγ)).mpr
    refine ⟨Eventually.of_forall (hki γ hγ),?_⟩
    apply (integrable_const (‖f‖*(B : ℝ))).mono'
      (hkmeas γ hγ).norm.integral_prod_right'
    filter_upwards [hmass] with t ht
    have he : (∫ x : ℝ, ‖k γ t x‖)=a γ t := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => Real.norm_of_nonneg (hknonneg γ hγ t x)
    rw [he,Real.norm_of_nonneg (integral_nonneg (hknonneg γ hγ t))]
    exact (le_abs_self (a γ t)).trans ((hanorm γ hγ t).trans
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) (norm_nonneg f)))
  have hmean (γ : NNReal) (hγ : γ≠0) :
      (∫ t : T, a γ t ∂ν)≤(Real.pi⁻¹*C*(γ : ℝ))*(∫ x : ℝ, f x) := by
    rw [show (∫ t : T, a γ t ∂ν)=∫ x : ℝ, ∫ t : T, k γ t x ∂ν from
      integral_integral_swap (hkiprod γ hγ)]
    rw [← integral_const_mul]
    apply integral_mono (hkiprod γ hγ).integral_prod_right (hfint.const_mul _)
    intro x
    simp only [k,integral_const_mul]
    by_cases hx : x∈U
    · nlinarith [mul_le_mul_of_nonneg_left (haverage x hx γ hγ)
        (mul_nonneg (hfnonneg x) (inv_nonneg.mpr Real.pi_pos.le))]
    · simp only [hfzero x hx,zero_mul,mul_zero,le_refl]
  let γ (n : ℕ) : NNReal := ⟨1/((n : ℝ)+1),by positivity⟩
  have hγne (n : ℕ) : γ n≠0 := by
    apply NNReal.coe_ne_zero.mp
    change 1/((n : ℝ)+1)≠0
    positivity
  have hγ : Tendsto (fun n => (γ n : ℝ)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have hlim (t : T) : Tendsto (fun n => a (γ n) t) atTop (𝓝 (g t)) := by
    simpa only [a,hkeq _ (hγne _),g] using
      tendsto_integral_cauchyRegularization (ρ t : Measure ℝ) f hγne hγ
  have hameas (n : ℕ) : AEStronglyMeasurable (a (γ n)) ν :=
    (hkmeas (γ n) (hγne n)).integral_prod_right'
  have hbound (n : ℕ) : ∀ᵐ t ∂ν, ‖a (γ n) t‖≤‖f‖*(B : ℝ) := by
    filter_upwards [hmass] with t ht
    exact (hanorm _ (hγne n) t).trans
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) (norm_nonneg f))
  have hlimit := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ : T => ‖f‖*(B : ℝ))
    hameas (integrable_const _) hbound (Eventually.of_forall hlim)
  have hzeroLim : Tendsto (fun n => (Real.pi⁻¹*C*(γ n : ℝ))*(∫ x : ℝ, f x))
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hγ.const_mul (Real.pi⁻¹*C)).mul_const (∫ x : ℝ,f x)
  have hzero : (∫ t : T, g t ∂ν)=0 := by
    apply le_antisymm (le_of_tendsto_of_tendsto hlimit hzeroLim
      (Eventually.of_forall fun n => hmean (γ n) (hγne n)))
    exact integral_nonneg fun t => integral_nonneg hfnonneg
  have hgmeas : AEStronglyMeasurable g ν :=
    aestronglyMeasurable_of_tendsto_ae atTop hameas (Eventually.of_forall hlim)
  have hgnorm : ∀ᵐ t ∂ν, ‖g t‖≤‖f‖*(B : ℝ) := by
    filter_upwards [hmass] with t ht
    have hh := norm_integral_le_of_norm_le_const (μ := (ρ t : Measure ℝ))
      (Eventually.of_forall fun x => f.norm_coe_le_norm x)
    have hm : (ρ t : Measure ℝ).real univ=((ρ t).mass : ℝ) := by
      rw [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
    exact (hh.trans_eq (congrArg (fun x : ℝ => ‖f‖*x) hm)).trans
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) (norm_nonneg f))
  have hgi : Integrable g ν := (integrable_const _).mono' hgmeas hgnorm
  exact (integral_eq_zero_iff_of_nonneg (fun t => integral_nonneg hfnonneg) hgi).mp hzero

end MeasureTheory
