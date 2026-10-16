import NLAlib.Probability.SubGaussian.GaussianDomination
import NLAlib.ForMathlib.Analysis.EvenConvex

/-!
# Affine norm profiles for Gaussian replacement

Even convex profiles implement finite contraction without a coupling or a
subgaussian-process comparison theorem. Source: the scalar domination reroute
in `random_matrices_probability_concentration_reroutes_2026_10_16.tex`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
namespace NLAlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def affineNormProfile (z a : E) (t : ℝ) : ℝ :=
  (‖z + t • a‖ + ‖z - t • a‖) / 2

private theorem affineNormProfile_even (z a : E) : Function.Even (affineNormProfile z a) := by
  intro t
  simp only [affineNormProfile, neg_smul, sub_eq_add_neg, neg_neg]
  ring

private theorem affineNormProfile_continuous (z a : E) : Continuous (affineNormProfile z a) := by
  unfold affineNormProfile
  fun_prop

private theorem convexOn_norm_add_smul (z a : E) :
    ConvexOn ℝ univ (fun t : ℝ => ‖z + t • a‖) := by
  let L : ℝ →ₗ[ℝ] E := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight a
  have h := convexOn_univ_norm.comp_affineMap
    (L.toAffineMap + AffineMap.const ℝ ℝ z)
  simpa [L, Function.comp_def, add_comm] using h

private theorem affineNormProfile_convex (z a : E) :
    ConvexOn ℝ univ (affineNormProfile z a) := by
  have hp := convexOn_norm_add_smul z a
  have hn : ConvexOn ℝ univ (fun t : ℝ => ‖z - t • a‖) := by
    simpa only [smul_neg, sub_eq_add_neg] using convexOn_norm_add_smul z (-a)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy α β hα hβ hab
  have hp' := hp.2 hx hy hα hβ hab
  have hn' := hn.2 hx hy hα hβ hab
  simp only [affineNormProfile, smul_eq_mul] at hp' hn' ⊢
  linarith

private theorem affineNormProfile_le (z a : E) (t : ℝ) :
    affineNormProfile z a t ≤ ‖z‖ + |t| * ‖a‖ := by
  have hp := norm_add_le z (t • a)
  have hn := norm_sub_le z (t • a)
  simp only [norm_smul, Real.norm_eq_abs] at hp hn
  unfold affineNormProfile
  linarith

private theorem affineNormProfile_nonneg (z a : E) (t : ℝ) :
    0 ≤ affineNormProfile z a t := by unfold affineNormProfile; positivity

private theorem integrable_norm_add_smul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) (z a : E) :
    Integrable (fun ω => ‖z + X ω • a‖) μ := by
  have hc : Continuous (fun t : ℝ => ‖z + t • a‖) := by fun_prop
  refine ((integrable_const ‖z‖).add (hX.norm.mul_const ‖a‖)).mono'
    (hc.measurable.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable ?_
  filter_upwards [] with ω
  change |‖z + X ω • a‖| ≤ ‖z‖ + |X ω| * ‖a‖
  rw [abs_of_nonneg (norm_nonneg _)]
  simpa only [norm_norm, norm_smul, Real.norm_eq_abs] using norm_add_le z (X ω • a)

private theorem integrable_affineNormProfile {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) (z a : E) :
    Integrable (fun ω => affineNormProfile z a (X ω)) μ := by
  have hp := integrable_norm_add_smul hX z a
  have hn := integrable_norm_add_smul hX.neg z a
  simpa only [affineNormProfile, Pi.add_apply, Pi.neg_apply, neg_smul, sub_eq_add_neg] using (hp.add hn).div_const 2

/-- The mean absolute standard Gaussian is at least two thirds. This coarse
explicit bound is enough for the tenfold scalar contraction constant. -/
theorem two_thirds_le_integral_abs_gaussianReal :
    (2 / 3 : ℝ) ≤ ∫ g : ℝ, |g| ∂gaussianReal 0 1 := by
  have h := integral_abs_rpow_gaussianReal (1 / 2) (by norm_num)
  have he : (∫ g : ℝ, |g| ∂gaussianReal 0 1) = Real.sqrt 2 / Real.sqrt Real.pi := by
    norm_num [Real.sqrt_eq_rpow] at h ⊢
    exact h
  rw [he, le_div_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsp := Real.sq_sqrt Real.pi_pos.le
  have hn2 := Real.sqrt_nonneg (2 : ℝ)
  have hnp := Real.sqrt_nonneg Real.pi
  nlinarith [Real.pi_lt_four]

private theorem affineNormProfile_abs (z a : E) (t : ℝ) :
    affineNormProfile z a |t| = affineNormProfile z a t := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, affineNormProfile_even z a t]

private theorem integral_affineNormProfile_gaussian (z a : E) (c : ℝ) :
    (∫ g : ℝ, affineNormProfile z a (c * g) ∂gaussianReal 0 1) =
      ∫ g : ℝ, ‖z + (c * g) • a‖ ∂gaussianReal 0 1 := by
  have hg : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hp := integrable_norm_add_smul (hg.const_mul c) z a
  have hn := integrable_norm_add_smul (hg.const_mul (-c)) z a
  simp only [id_eq] at hp hn
  have he : (∫ g : ℝ, ‖z - (c * g) • a‖ ∂gaussianReal 0 1) =
      ∫ g : ℝ, ‖z + (c * g) • a‖ ∂gaussianReal 0 1 := by
    have hneg : (gaussianReal 0 1).map (fun g : ℝ => -g) = gaussianReal 0 1 := by
      simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
    calc
      _ = ∫ g : ℝ, ‖z + (c * (-g)) • a‖ ∂gaussianReal 0 1 := by
        congr 1; funext g; rw [mul_neg, neg_smul, sub_eq_add_neg]
      _ = _ := by
        rw [← integral_map (φ := fun g : ℝ => -g)
          (f := fun g : ℝ => ‖z + (c * g) • a‖) (by fun_prop) (by fun_prop), hneg]
  unfold affineNormProfile
  rw [integral_div, integral_add hp (by simpa only [neg_mul, neg_smul, sub_eq_add_neg] using hn), he]
  ring

private theorem integral_norm_add_smul_le_copy_profile {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : Integrable (id : ℝ → ℝ) ν)
    (hmean : ∫ x : ℝ, x ∂ν = 0) (z a : E) :
    (∫ x : ℝ, ‖z + x • a‖ ∂ν) ≤
      ∫ p : ℝ × ℝ, affineNormProfile z a (p.1 - p.2) ∂ν.prod ν := by
  have hd : Integrable (fun p : ℝ × ℝ => p.1 - p.2) (ν.prod ν) :=
    (hν.comp_fst ν).sub (hν.comp_snd ν)
  have hpd := integrable_norm_add_smul hd z a
  have hnd := integrable_norm_add_smul hd.neg z a
  have hsym : (∫ p : ℝ × ℝ, ‖z - (p.1 - p.2) • a‖ ∂ν.prod ν) =
      ∫ p : ℝ × ℝ, ‖z + (p.1 - p.2) • a‖ ∂ν.prod ν := by
    have hs := integral_prod_swap (μ := ν) (ν := ν)
      (fun p : ℝ × ℝ => ‖z + (p.1 - p.2) • a‖)
    convert hs using 1
    congr 1; funext p
    simp only [Prod.fst_swap, Prod.snd_swap]
    congr 1
    module
  have hbound : (∫ x : ℝ, ‖z + x • a‖ ∂ν) ≤
      ∫ p : ℝ × ℝ, ‖z + (p.1 - p.2) • a‖ ∂ν.prod ν := by
    rw [integral_prod _ hpd]
    refine integral_mono (integrable_norm_add_smul hν z a) hpd.integral_prod_left ?_
    intro x
    have hy := (integrable_const x).sub hν
    have hj := (convexOn_norm_add_smul z a).map_integral_le
      (by fun_prop) isClosed_univ (ae_of_all ν fun _ => mem_univ _) hy
      (integrable_norm_add_smul hy z a)
    change ‖z + (∫ y : ℝ, x - y ∂ν) • a‖ ≤ _ at hj
    have hνi : Integrable (fun y : ℝ => y) ν :=
      hν.congr (ae_of_all ν fun y => rfl)
    rw [integral_sub (integrable_const x) hνi, integral_const, probReal_univ,
      one_smul, hmean, sub_zero] at hj
    simpa only [Pi.sub_apply, id_eq] using hj
  have he : (∫ p : ℝ × ℝ, affineNormProfile z a (p.1 - p.2) ∂ν.prod ν) =
      ∫ p : ℝ × ℝ, ‖z + (p.1 - p.2) • a‖ ∂ν.prod ν := by
    unfold affineNormProfile
    rw [integral_div, integral_add hpd
      (by simpa only [Pi.neg_apply, neg_smul, sub_eq_add_neg] using hnd), hsym]
    ring
  rwa [he]

private theorem integral_shifted_gaussian_profile_le (z a : E) {K : ℝ} (hK : 0 < K) :
    (∫ g : ℝ, affineNormProfile z a (4 * K * (1 + |g|)) ∂gaussianReal 0 1) ≤
      ∫ g : ℝ, ‖z + (10 * K * g) • a‖ ∂gaussianReal 0 1 := by
  let γ := gaussianReal 0 1
  have hg : Integrable (id : ℝ → ℝ) γ := (memLp_id_gaussianReal 1).integrable le_rfl
  have hga : Integrable (fun g : ℝ => |g|) γ := by simpa only [Real.norm_eq_abs, id_eq] using hg.norm
  have hw := (integrable_const (1 : ℝ)).add hga |>.const_mul (4 * K)
  have ht := hga.const_mul (10 * K)
  have hwi := integrable_affineNormProfile hw z a
  have hti := integrable_affineNormProfile ht z a
  have hc := affineNormProfile_convex z a
  have hpt (g : ℝ) : affineNormProfile z a (4 * K * (1 + |g|)) ≤
      (3 / 5 : ℝ) * affineNormProfile z a ((20 / 3 : ℝ) * K) +
        (2 / 5 : ℝ) * affineNormProfile z a (10 * K * |g|) := by
    have h := hc.2 (mem_univ ((20 / 3 : ℝ) * K)) (mem_univ (10 * K * |g|))
      (by norm_num : (0 : ℝ) ≤ 3 / 5) (by norm_num : (0 : ℝ) ≤ 2 / 5)
      (by norm_num : (3 / 5 : ℝ) + 2 / 5 = 1)
    simp only [smul_eq_mul] at h
    convert h using 1 <;> congr 1 <;> ring
  have hi := integral_mono hwi
    ((integrable_const ((3 / 5 : ℝ) * affineNormProfile z a ((20 / 3 : ℝ) * K))).add
      (hti.const_mul (2 / 5 : ℝ))) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const _) (hti.const_mul _), integral_const,
    probReal_univ, one_smul, integral_const_mul] at hi
  have hj := hc.map_integral_le (affineNormProfile_continuous z a).continuousOn
    isClosed_univ (ae_of_all γ fun _ => mem_univ _) ht hti
  rw [integral_const_mul] at hj
  have hm := hc.monotoneOn_nonneg_of_even (affineNormProfile_even z a)
  have hJ : (2 / 3 : ℝ) ≤ ∫ g : ℝ, |g| ∂γ := two_thirds_le_integral_abs_gaussianReal
  have hs : affineNormProfile z a ((20 / 3 : ℝ) * K) ≤
      affineNormProfile z a (10 * K * ∫ g : ℝ, |g| ∂γ) :=
    hm (by change 0 ≤ (20 / 3 : ℝ) * K; positivity)
      (by change 0 ≤ 10 * K * ∫ g : ℝ, |g| ∂γ; positivity) (by nlinarith)
  have he : (∫ g : ℝ, affineNormProfile z a (10 * K * |g|) ∂γ) =
      ∫ g : ℝ, ‖z + (10 * K * g) • a‖ ∂γ := by
    calc
      _ = ∫ g : ℝ, affineNormProfile z a (10 * K * g) ∂γ := by
        apply integral_congr_ae
        filter_upwards [] with g
        rw [show 10 * K * |g| = |10 * K * g| by
          rw [abs_mul, abs_of_pos (show 0 < 10 * K by positivity)]]
        exact affineNormProfile_abs z a _
      _ = _ := integral_affineNormProfile_gaussian z a (10 * K)
  rw [← he]
  linarith

/-- A centered scalar coefficient with square-exponential parameter `K` can be
replaced by a Gaussian coefficient of scale `10K` inside any affine norm.
All integrability follows from the actual nonnegative exponential moment.
Source: the scalar domination reroute, finite convex contraction argument. -/
theorem integral_norm_add_smul_le_gaussian_of_lintegral_exp_sq
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (K : ℝ) (hK : 0 < K)
    (hmean : ∫ x : ℝ, x ∂ν = 0)
    (hpsi : ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν ≤ 2)
    (z a : E) :
    (∫ x : ℝ, ‖z + x • a‖ ∂ν) ≤
      ∫ g : ℝ, ‖z + (10 * K * g) • a‖ ∂gaussianReal 0 1 := by
  have hν : Integrable (id : ℝ → ℝ) ν :=
    (hasSubgaussianMGF_of_lintegral_exp_sq_le_two aemeasurable_id K hK hmean hpsi).memLp 1
      |>.integrable le_rfl
  have hd : Integrable (fun p : ℝ × ℝ => p.1 - p.2) (ν.prod ν) :=
    (hν.comp_fst ν).sub (hν.comp_snd ν)
  let W : ℝ → ℝ := fun g => 4 * K * (1 + |g|)
  let f : ℝ → ℝ := fun t => affineNormProfile z a (max t 0)
  have hfc : Continuous f := (affineNormProfile_continuous z a).comp (continuous_id.max continuous_const)
  have hfm : Monotone f := by
    intro s t hst
    change affineNormProfile z a (max s 0) ≤ affineNormProfile z a (max t 0)
    apply (affineNormProfile_convex z a).monotoneOn_nonneg_of_even (affineNormProfile_even z a)
    · exact le_max_right s 0
    · exact le_max_right t 0
    · exact max_le_max hst le_rfl
  have hg : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hW : Integrable W (gaussianReal 0 1) := by
    simpa only [W, Real.norm_eq_abs, id_eq, Pi.add_apply] using
      ((integrable_const (1 : ℝ)).add hg.norm).const_mul (4 * K)
  have hc := lintegral_comp_le_of_measure_lt_le hd.aemeasurable.norm hW.aemeasurable
    (fun t => measure_abs_gt_le_gaussian_shift_of_lintegral_exp_sq
      hd.aemeasurable hK (lintegral_exp_sub_sq_le_two hK hpsi) t)
    hfc hfm (fun t => affineNormProfile_nonneg z a _)
  have hleft (p : ℝ × ℝ) : f |p.1 - p.2| = affineNormProfile z a (p.1 - p.2) := by
    dsimp [f]
    rw [max_eq_left (abs_nonneg _), affineNormProfile_abs]
  have hright (g : ℝ) : f (W g) = affineNormProfile z a (W g) := by
    dsimp [f]
    rw [max_eq_left (by dsimp [W]; positivity)]
  simp only [Real.norm_eq_abs] at hc
  simp_rw [hleft, hright] at hc
  have hdi := integrable_affineNormProfile hd z a
  have hWi := integrable_affineNormProfile hW z a
  rw [← ofReal_integral_eq_lintegral_ofReal hdi (ae_of_all _ fun _ => affineNormProfile_nonneg z a _),
    ← ofReal_integral_eq_lintegral_ofReal hWi (ae_of_all _ fun _ => affineNormProfile_nonneg z a _)] at hc
  have hb : (∫ p : ℝ × ℝ, affineNormProfile z a (p.1 - p.2) ∂ν.prod ν) ≤
      ∫ g : ℝ, affineNormProfile z a (W g) ∂gaussianReal 0 1 :=
    (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => affineNormProfile_nonneg z a _)).mp hc
  exact (integral_norm_add_smul_le_copy_profile hν hmean z a).trans
    (hb.trans (integral_shifted_gaussian_profile_le z a hK))

end NLAlib
