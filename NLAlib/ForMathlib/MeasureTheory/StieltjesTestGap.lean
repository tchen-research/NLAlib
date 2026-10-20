import NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesSupport

/-! # Uniform Stieltjes bounds from almost-everywhere positive test gaps

A positive compact test gives an actual scalar measure gap. Uniform mass
then bounds the transform over that gap. Continuity in the parameter
extends the bound from almost every parameter to the actual support.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace MeasureTheory

/-- Actual separation of a finite real measure from the real part of the
evaluation point gives the native reciprocal-distance Stieltjes bound. -/
theorem norm_integral_real_cauchyKernel_le_of_ae_dist_ge
    (μ : Measure ℝ) [IsFiniteMeasure μ] (x a : ℝ) (ha : 0<a) (z : ℂ)
    (hzre : z.re=x) (hsep : ∀ᵐ ξ : ℝ ∂μ, a≤|ξ-x|) :
    ‖∫ ξ : ℝ, ((ξ : ℂ)-z)⁻¹ ∂μ‖≤a⁻¹*μ.real univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hsep] with ξ hξ
  have hnorm : a≤‖(ξ : ℂ)-z‖ := by
    have hre : |ξ-x|≤‖(ξ : ℂ)-z‖ := by
      simpa only [Complex.sub_re,Complex.ofReal_re,hzre] using
        Complex.abs_re_le_norm ((ξ : ℂ)-z)
    exact hξ.trans hre
  rw [norm_inv]
  exact (inv_le_inv₀ (ha.trans_le hnorm) ha).mpr hnorm

/-- A genuine real measure gap gives the exact O(height) bound for the
imaginary Stieltjes transform. Every inverse and integral is native. -/
theorem im_integral_real_cauchyKernel_le_of_ae_dist_ge
    (μ : Measure ℝ) [IsFiniteMeasure μ] (x a : ℝ) (ha : 0<a)
    (γ : NNReal) (hγ : γ≠0) (hsep : ∀ᵐ ξ : ℝ ∂μ, a≤|ξ-x|) :
    (∫ ξ : ℝ, ((ξ : ℂ)-((x : ℂ)+(γ : ℝ)*Complex.I))⁻¹ ∂μ).im≤
      ((γ : ℝ)/a^2)*μ.real univ := by
  have hγpos : 0<(γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have hz : 0<((x : ℂ)+(γ : ℝ)*Complex.I).im := by simpa using hγpos
  change RCLike.im (∫ ξ : ℝ, ((ξ : ℂ)-((x : ℂ)+(γ : ℝ)*Complex.I))⁻¹ ∂μ)≤_
  rw [← integral_im (Complex.integrable_real_cauchyKernel μ hz)]
  calc
    _ ≤ ∫ _ξ : ℝ, (γ : ℝ)/a^2 ∂μ := by
      apply integral_mono_ae (Complex.integrable_real_cauchyKernel μ hz).im (integrable_const _)
      filter_upwards [hsep] with ξ hξ
      have hs : a^2≤(ξ-x)^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ ha.le hξ 2
      have hden : a^2≤(ξ-x)^2+(γ : ℝ)^2 := hs.trans (le_add_of_nonneg_right (sq_nonneg _))
      have he : (((ξ : ℂ)-((x : ℂ)+(γ : ℝ)*Complex.I))⁻¹).im=
          (γ : ℝ)/((ξ-x)^2+(γ : ℝ)^2) := by
        simp only [Complex.inv_im,Complex.sub_im,Complex.ofReal_im,Complex.add_im,
          Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
          zero_add,add_zero,zero_sub,neg_neg,Complex.normSq_apply,Complex.sub_re,
          Complex.add_re,Complex.mul_re,sub_zero]
        ring
      change (((ξ : ℂ)-((x : ℂ)+(γ : ℝ)*Complex.I))⁻¹).im≤_
      rw [he]
      exact div_le_div_of_nonneg_left hγpos.le (sq_pos_of_pos ha) hden
    _ = _ := by rw [integral_const,smul_eq_mul,mul_comm]
/-- A zero integral of a nonnegative test which is at least one on a
ball gives a genuine measure gap and the reciprocal-distance bound for
its Stieltjes transform. This includes zero measures and arbitrary
imaginary heights. -/
theorem norm_stieltjes_le_of_zero_positive_test
    (ρ : FiniteMeasure ℝ) (f : ℝ →ᵇ ℝ) (hfnonneg : ∀ ξ, 0≤f ξ)
    (hzero : ∫ ξ : ℝ, f ξ ∂(ρ : Measure ℝ)=0)
    (x a : ℝ) (ha : 0<a) (hfone : ∀ ξ, |ξ-x|<a → 1≤f ξ)
    (z : ℂ) (hzre : z.re=x) :
    ‖∫ ξ : ℝ, ((ξ : ℂ)-z)⁻¹ ∂(ρ : Measure ℝ)‖≤a⁻¹*(ρ.mass : ℝ) := by
  have hi : Integrable f (ρ : Measure ℝ) :=
    (integrable_const ‖f‖).mono' f.continuous.aestronglyMeasurable
      (Eventually.of_forall fun ξ => f.norm_coe_le_norm ξ)
  have hfzero := (integral_eq_zero_iff_of_nonneg hfnonneg hi).mp hzero
  have hsep : ∀ᵐ ξ : ℝ ∂(ρ : Measure ℝ), a≤|ξ-x| := by
    filter_upwards [hfzero] with ξ hξ
    change f ξ=0 at hξ
    apply le_of_not_gt
    intro ht
    have hh := hfone ξ ht
    rw [hξ] at hh
    linarith
  have hh := norm_integral_real_cauchyKernel_le_of_ae_dist_ge (ρ : Measure ℝ) x a ha z hzre hsep
  simpa only [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal] using hh

/-- Continuous actual Stieltjes transforms and a uniform native mass
bound extend an almost-everywhere positive-test gap estimate to every
parameter in the true support of its law. No weakly continuous
measure-valued kernel or pointwise gap premise is assumed. -/
theorem norm_stieltjes_family_le_on_support_of_ae_zero_positive_test
    {T : Type*} [MeasurableSpace T] [TopologicalSpace T]
    (ν : Measure T) (ρ : T → FiniteMeasure ℝ) (r : T → ℂ → ℂ)
    (hrep : ∀ t : T, ∀ z : ℂ, 0<z.im → r t z=
      ∫ ξ : ℝ, ((ξ : ℂ)-z)⁻¹ ∂(ρ t : Measure ℝ))
    (hc : ∀ z : ℂ, 0<z.im → Continuous (fun t : T => r t z))
    (B : NNReal) (hmass : ∀ᵐ t ∂ν, (ρ t).mass≤B)
    (f : ℝ →ᵇ ℝ) (hfnonneg : ∀ ξ, 0≤f ξ)
    (hzero : ∀ᵐ t ∂ν, ∫ ξ : ℝ, f ξ ∂(ρ t : Measure ℝ)=0)
    (x a : ℝ) (ha : 0<a) (hfone : ∀ ξ, |ξ-x|<a → 1≤f ξ)
    (t : T) (ht : t∈ν.support) (z : ℂ) (hz : 0<z.im) (hzre : z.re=x) :
    ‖r t z‖≤a⁻¹*(B : ℝ) := by
  have he : ∀ᵐ u ∂ν, ‖r u z‖≤a⁻¹*(B : ℝ) := by
    filter_upwards [hmass,hzero] with u huM hu0
    rw [hrep u z hz]
    exact (norm_stieltjes_le_of_zero_positive_test (ρ u) f hfnonneg hu0 x a ha hfone z hzre).trans
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr huM) (inv_nonneg.mpr ha.le))
  exact Measure.support_subset_of_isClosed
    (isClosed_le (hc z hz).norm continuous_const) he ht

end MeasureTheory
