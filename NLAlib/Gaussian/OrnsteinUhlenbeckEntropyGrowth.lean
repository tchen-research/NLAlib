import NLAlib.Gaussian.OrnsteinUhlenbeckGrowth
import NLAlib.ForMathlib.Analysis.DerivativeLimit
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic

/-!
# Entropy dissipation on the positive polynomial-growth domain

Atlas: `ornstein-uhlenbeck`. The bounded-value/bounded-derivative result in
NLAlib is applied to positive compactly supported perturbations of a
constant. Uniform polynomial dominators pass entropy and Fisher
information through the Mehler operator and the outer Gaussian integral.
FTC then transfers the derivative identity.

Source: Bakry--Gentil--Ledoux 2014, §5.7; Ledoux, §5.1. The smooth cutoff
construction is adapted from NLAlib's `LogSobolevOneDim.lean`, commit
`d4d0a69f38f309825f228917b75f9a2a33a91faa`. This is a concrete
polynomial-growth class, not an assertion about every C1 function merely
bounded below.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set

namespace NLAlib

/-- Ornstein--Uhlenbeck entropy dissipation for positive C1 functions whose
values and first derivatives have polynomial growth. Both source upper
bounds are removed; all Gaussian integrability and limiting dominators
are proved. Source: Bakry--Gentil--Ledoux 2014, §5.7; Ledoux, §5.1.
Atlas: `ornstein-uhlenbeck`. This theorem concerns the standard Gaussian
line and a common explicit polynomial majorant for `f` and `f'`. -/
theorem hasDerivAt_integral_ornsteinUhlenbeck_mul_log_of_polynomial_growth
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (δ C : ℝ) (d : ℕ)
    (hδ : 0 < δ) (hlow : ∀ x, δ ≤ f x)
    (hValue : ∀ x, |f x| ≤ C * (1 + |x|) ^ d)
    (hDeriv : ∀ x, |deriv f x| ≤ C * (1 + |x|) ^ d)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun s => ∫ x, ornsteinUhlenbeck s f x * Real.log (ornsteinUhlenbeck s f x)
        ∂(gaussianReal 0 1))
      (-∫ x, deriv (ornsteinUhlenbeck t f) x ^ 2 / ornsteinUhlenbeck t f x
        ∂(gaussianReal 0 1)) t := by
  have hCδ : δ ≤ C := by
    have h := hValue 0
    simp only [abs_zero, add_zero, one_pow, mul_one] at h
    exact (hlow 0).trans ((le_abs_self _).trans h)
  have hC : 0 ≤ C := hδ.le.trans hCδ
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hχc : ContDiff ℝ 1 (fun x => χ x) := χ.contDiff
  have hχd : Continuous (deriv (fun x => χ x)) := hχc.continuous_deriv le_rfl
  obtain ⟨K, hK⟩ := hχd.bounded_above_of_compact_support χ.hasCompactSupport.deriv
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hχ0 : χ (0 : ℝ) = 1 := by
    apply χ.one_of_mem_closedBall
    simp [χ]
  let cut : ℕ → ℝ → ℝ := fun n x => χ (x / ((n : ℝ) + 1))
  let gN : ℕ → ℝ → ℝ := fun n x => (f x - δ) * cut n x
  let fN : ℕ → ℝ → ℝ := fun n x => δ + gN n x
  let D := C * (1 + K)
  have hnpos (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcutcd (n : ℕ) : ContDiff ℝ 1 (cut n) := hχc.comp (contDiff_id.div_const _)
  have hcut01 (n : ℕ) (x : ℝ) : 0 ≤ cut n x ∧ cut n x ≤ 1 := ⟨χ.nonneg, χ.le_one⟩
  have hgNcd (n : ℕ) : ContDiff ℝ 1 (gN n) := (hf.sub contDiff_const).mul (hcutcd n)
  have hfNcd (n : ℕ) : ContDiff ℝ 1 (fN n) := contDiff_const.add (hgNcd n)
  have hfNlow (n : ℕ) (x : ℝ) : δ ≤ fN n x := by
    have h1 := hlow x
    have h2 := (hcut01 n x).1
    dsimp [fN, gN]
    nlinarith
  have hfNup (n : ℕ) (x : ℝ) : fN n x ≤ f x := by
    have h1 := hlow x
    have h2 := (hcut01 n x).2
    dsimp [fN, gN]
    nlinarith
  have hfNValue (n : ℕ) (x : ℝ) : |fN n x| ≤ C * (1 + |x|) ^ d := by
    rw [abs_of_pos (lt_of_lt_of_le hδ (hfNlow n x))]
    exact (hfNup n x).trans ((le_abs_self _).trans (hValue x))
  have hcutDeriv (n : ℕ) (x : ℝ) : deriv (cut n) x =
      deriv (fun x => χ x) (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
    have h1 := (hasDerivAt_id x).div_const ((n : ℝ) + 1)
    have h2 := ((hχc.differentiable one_ne_zero) (x / ((n : ℝ) + 1))).hasDerivAt.comp x h1
    exact h2.deriv.trans (by ring)
  have hcutDerivBound (n : ℕ) (x : ℝ) : |deriv (cut n) x| ≤ K := by
    rw [hcutDeriv, abs_div, abs_of_pos (hnpos n)]
    have h := hK (x / ((n : ℝ) + 1))
    rw [Real.norm_eq_abs] at h
    calc
      _ ≤ K / 1 := by gcongr; linarith [Nat.cast_nonneg (α := ℝ) n]
      _ = K := div_one K
  have hfNDeriv (n : ℕ) (x : ℝ) : deriv (fN n) x =
      deriv f x * cut n x + (f x - δ) * deriv (cut n) x := by
    have h := (((hf.differentiable one_ne_zero) x).hasDerivAt.sub_const δ).mul
      (((hcutcd n).differentiable one_ne_zero) x).hasDerivAt
    exact (h.const_add δ).deriv
  have hfNDerivBound (n : ℕ) (x : ℝ) : |deriv (fN n) x| ≤ D * (1 + |x|) ^ d := by
    have hW : 0 ≤ C * (1 + |x|) ^ d := by positivity
    have hsub : |f x - δ| ≤ C * (1 + |x|) ^ d := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hlow x))]
      have h := (le_abs_self (f x)).trans (hValue x)
      linarith
    rw [hfNDeriv]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hc : |cut n x| ≤ 1 := by rw [abs_of_nonneg (hcut01 n x).1]; exact (hcut01 n x).2
    have h1 := mul_le_mul (hDeriv x) hc (abs_nonneg _) hW
    have h2 := mul_le_mul hsub (hcutDerivBound n x) (abs_nonneg _) hW
    dsimp [D]
    nlinarith
  have hgNsupp (n : ℕ) : HasCompactSupport (gN n) := by
    apply HasCompactSupport.mul_left
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * ((n : ℝ) + 1)))
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    apply χ.zero_of_le_dist
    rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos (hnpos n),
      le_div_iff₀ (hnpos n)]
    exact hx.le
  have hfNbounded (n : ℕ) : ∃ Bn : ℝ,
      (∀ x, fN n x ≤ Bn) ∧ (∀ x, |deriv (fN n) x| ≤ Bn) := by
    obtain ⟨Bv, hBv⟩ := (hgNcd n).continuous.bounded_above_of_compact_support (hgNsupp n)
    obtain ⟨Bd, hBd⟩ := ((hgNcd n).continuous_deriv le_rfl).bounded_above_of_compact_support
      (hgNsupp n).deriv
    have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
    have hBd0 : 0 ≤ Bd := (norm_nonneg _).trans (hBd 0)
    refine ⟨δ + Bv + Bd, ?_, ?_⟩
    · intro x
      have h := hBv x
      rw [Real.norm_eq_abs] at h
      have ha := le_abs_self (gN n x)
      dsimp [fN]
      linarith
    · intro x
      have he : deriv (fN n) x = deriv (gN n) x :=
        ((((hgNcd n).differentiable one_ne_zero) x).hasDerivAt.const_add δ).deriv
      rw [he]
      have h := hBd x
      rw [Real.norm_eq_abs] at h
      linarith
  have hsmall : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have harg (x : ℝ) : Tendsto (fun n : ℕ => x / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_const_nhds (x := x)).mul hsmall
  have hcutlim (x : ℝ) : Tendsto (fun n => cut n x) atTop (nhds 1) := by
    simpa only [cut, Function.comp_def, hχ0] using (hχc.continuous.tendsto (0 : ℝ)).comp (harg x)
  have hcutDerivlim (x : ℝ) : Tendsto (fun n => deriv (cut n) x) atTop (nhds 0) := by
    have h := ((hχd.tendsto (0 : ℝ)).comp (harg x)).mul hsmall
    simp_rw [hcutDeriv]
    simpa only [Function.comp_def, div_eq_mul_inv, one_div, one_mul, mul_zero] using h
  have hfNlim (x : ℝ) : Tendsto (fun n => fN n x) atTop (nhds (f x)) := by
    have h := (tendsto_const_nhds (x := δ)).add
      ((tendsto_const_nhds (x := f x - δ)).mul (hcutlim x))
    have he : δ + (f x - δ) * 1 = f x := by ring
    simpa only [fN, gN, he] using h
  have hfNDerivlim (x : ℝ) : Tendsto (fun n => deriv (fN n) x) atTop (nhds (deriv f x)) := by
    have h := ((tendsto_const_nhds (x := deriv f x)).mul (hcutlim x)).add
      ((tendsto_const_nhds (x := f x - δ)).mul (hcutDerivlim x))
    simpa only [← hfNDeriv, mul_one, mul_zero, add_zero] using h
  let E : ℝ → ℝ := fun s => ∫ x,
    ornsteinUhlenbeck s f x * Real.log (ornsteinUhlenbeck s f x) ∂(gaussianReal 0 1)
  let EN : ℕ → ℝ → ℝ := fun n s => ∫ x,
    ornsteinUhlenbeck s (fN n) x * Real.log (ornsteinUhlenbeck s (fN n) x) ∂(gaussianReal 0 1)
  let J : ℝ → ℝ := fun s => ∫ x, ornsteinUhlenbeckFisherIntegrand s f x ∂(gaussianReal 0 1)
  let JN : ℕ → ℝ → ℝ := fun n s =>
    ∫ x, ornsteinUhlenbeckFisherIntegrand s (fN n) x ∂(gaussianReal 0 1)
  let M := ∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1)
  let B := (D * M) ^ 2 / δ * ∫ x : ℝ, (1 + |x|) ^ (2 * d) ∂(gaussianReal 0 1)
  have hENderiv (n : ℕ) (s : ℝ) (hs : 0 < s) : HasDerivAt (EN n) (-JN n s) s := by
    obtain ⟨Bn, hBn, hDn⟩ := hfNbounded n
    have h := hasDerivAt_integral_ornsteinUhlenbeck_mul_log
      (fN n) (hfNcd n) δ Bn hδ (hfNlow n) hBn hDn s hs
    apply h.congr_deriv
    change -(∫ x, deriv (ornsteinUhlenbeck s (fN n)) x ^ 2 / ornsteinUhlenbeck s (fN n) x
      ∂(gaussianReal 0 1)) = -(∫ x,
        ornsteinUhlenbeckFisherIntegrand s (fN n) x ∂(gaussianReal 0 1))
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change deriv (ornsteinUhlenbeck s (fN n)) x ^ 2 / ornsteinUhlenbeck s (fN n) x =
        ornsteinUhlenbeckFisherIntegrand s (fN n) x
      rw [(hasDerivAt_ornsteinUhlenbeck (fN n) (hfNcd n) Bn hDn s x).deriv]
      rfl
  have hENlim (s : ℝ) (hs : 0 < s) : Tendsto (fun n => EN n s) atTop (nhds (E s)) := by
    change Tendsto (fun n => ∫ x, ornsteinUhlenbeck s (fN n) x *
      Real.log (ornsteinUhlenbeck s (fN n) x) ∂(gaussianReal 0 1)) atTop
      (nhds (∫ x, ornsteinUhlenbeck s f x * Real.log (ornsteinUhlenbeck s f x) ∂(gaussianReal 0 1)))
    refine tendsto_integral_of_dominated_convergence
      (fun x => (C * M) ^ 2 * (1 + |x|) ^ (2 * d) + 1)
      (fun n => by
        have hm : Measurable (ornsteinUhlenbeck s (fN n)) :=
          (measurable_ornsteinUhlenbeck_joint (hfNcd n).continuous.measurable).comp
          (measurable_const.prodMk measurable_id)
        exact (hm.mul hm.log).aestronglyMeasurable)
      (((integrable_one_add_abs_pow_gaussianReal (2 * d)).const_mul _).add (integrable_const _))
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs]
      have hu : 0 ≤ ornsteinUhlenbeck s (fN n) x := hδ.le.trans
        (le_ornsteinUhlenbeck_of_polynomial_growth (hfNcd n).continuous.measurable
          C d (hfNValue n) δ (hfNlow n) s x)
      have hlog := abs_mul_log_le_sq_add_one (ornsteinUhlenbeck s (fN n) x) hu
      have h := abs_ornsteinUhlenbeck_le_polynomial (hfNcd n).continuous.measurable
        C d (hfNValue n) s x hs.le
      have hsq : ornsteinUhlenbeck s (fN n) x ^ 2 ≤ (C * M) ^ 2 * (1 + |x|) ^ (2 * d) := by
        simpa only [sq_abs, mul_pow, ← pow_mul, Nat.mul_comm] using
          pow_le_pow_left₀ (abs_nonneg _) h 2
      linarith
    · exact (Real.continuous_mul_log.tendsto (ornsteinUhlenbeck s f x)).comp
        (tendsto_ornsteinUhlenbeck_of_polynomial_bound fN f
          (fun n => (hfNcd n).continuous.measurable) C d hfNValue hfNlim s x)
  have hJNlim (s : ℝ) (hs : 0 < s) : Tendsto (fun n => JN n s) atTop (nhds (J s)) := by
    change Tendsto (fun n => ∫ x,
      ornsteinUhlenbeckFisherIntegrand s (fN n) x ∂(gaussianReal 0 1)) atTop
      (nhds (∫ x, ornsteinUhlenbeckFisherIntegrand s f x ∂(gaussianReal 0 1)))
    refine tendsto_integral_of_dominated_convergence
      (fun x => (D * M) ^ 2 / δ * (1 + |x|) ^ (2 * d))
      (fun n => ((measurable_ornsteinUhlenbeckFisherIntegrand_joint
        (hfNcd n).continuous.measurable).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      ((integrable_one_add_abs_pow_gaussianReal (2 * d)).const_mul _)
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs]
      exact abs_ornsteinUhlenbeckFisherIntegrand_le (hfNcd n).continuous.measurable
        C D d (hfNValue n) (hfNDerivBound n) δ hδ (hfNlow n) s x hs.le
    · have h1 := tendsto_ornsteinUhlenbeck_of_polynomial_bound fN f
        (fun n => (hfNcd n).continuous.measurable) C d hfNValue hfNlim s x
      have h2 := tendsto_ornsteinUhlenbeck_of_polynomial_bound (fun n => deriv (fN n)) (deriv f)
        (fun n => measurable_deriv _) D d hfNDerivBound hfNDerivlim s x
      have hp : ornsteinUhlenbeck s f x ≠ 0 := (lt_of_lt_of_le hδ
        (le_ornsteinUhlenbeck_of_polynomial_growth hf.continuous.measurable
          C d hValue δ hlow s x)).ne'
      exact ((h2.const_mul (Real.exp (-s))).pow 2).div h1 hp
  have hDmeas (n : ℕ) : Measurable (fun s => -JN n s) :=
    (measurable_integral_ornsteinUhlenbeckFisherIntegrand (hfNcd n).continuous.measurable).neg
  have hdmeas : Measurable (fun s => -J s) :=
    (measurable_integral_ornsteinUhlenbeckFisherIntegrand hf.continuous.measurable).neg
  have hdcont : ContinuousOn (fun s => -J s) (Ioi 0) := by
    intro s hs
    exact (continuousAt_integral_ornsteinUhlenbeckFisherIntegrand f hf C C d hValue hDeriv
      δ hδ hlow s hs).neg.continuousWithinAt
  have hDbound (n : ℕ) (s : ℝ) (hs : 0 < s) : |-JN n s| ≤ B := by
    rw [abs_neg]
    exact abs_integral_ornsteinUhlenbeckFisherIntegrand_le (hfNcd n).continuous.measurable
      C D d (hfNValue n) (hfNDerivBound n) δ hδ (hfNlow n) s hs.le
  have hmain := hasDerivAt_of_pointwise_tendsto_of_bounded_derivatives EN
    (fun n s => -JN n s) E (fun s => -J s) B hDmeas hdmeas hdcont
    hENderiv hDbound hENlim (fun s hs => (hJNlim s hs).neg) t ht
  apply hmain.congr_deriv
  change -(∫ x, ornsteinUhlenbeckFisherIntegrand t f x ∂(gaussianReal 0 1)) =
    -(∫ x, deriv (ornsteinUhlenbeck t f) x ^ 2 / ornsteinUhlenbeck t f x ∂(gaussianReal 0 1))
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => ornsteinUhlenbeckFisherIntegrand_eq f hf C d hValue hDeriv t x

/-- The derivative of the full entropy, including its mean-normalization
term, is minus the Fisher information on the positive polynomial-growth
domain. Gaussian invariance makes the normalization term constant in
time. Source: Bakry--Gentil--Ledoux 2014, §5.7; Ledoux, §5.1.
Atlas: `ornstein-uhlenbeck`. -/
theorem hasDerivAt_entropy_ornsteinUhlenbeck_of_polynomial_growth
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (δ C : ℝ) (d : ℕ)
    (hδ : 0 < δ) (hlow : ∀ x, δ ≤ f x)
    (hValue : ∀ x, |f x| ≤ C * (1 + |x|) ^ d)
    (hDeriv : ∀ x, |deriv f x| ≤ C * (1 + |x|) ^ d)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s =>
      (∫ x, ornsteinUhlenbeck s f x * Real.log (ornsteinUhlenbeck s f x) ∂(gaussianReal 0 1)) -
        (∫ x, ornsteinUhlenbeck s f x ∂(gaussianReal 0 1)) *
          Real.log (∫ x, ornsteinUhlenbeck s f x ∂(gaussianReal 0 1)))
      (-∫ x, deriv (ornsteinUhlenbeck t f) x ^ 2 / ornsteinUhlenbeck t f x
        ∂(gaussianReal 0 1)) t := by
  have hi := integrable_gaussianReal_of_polynomial_growth hf.continuous.measurable.aemeasurable C d hValue
  have h := (hasDerivAt_integral_ornsteinUhlenbeck_mul_log_of_polynomial_growth
    f hf δ C d hδ hlow hValue hDeriv t ht).sub_const
    ((∫ x, f x ∂(gaussianReal 0 1)) * Real.log (∫ x, f x ∂(gaussianReal 0 1)))
  apply h.congr_of_eventuallyEq
  have hnear : ∀ᶠ s in nhds t, 0 < s := isOpen_Ioi.mem_nhds ht
  filter_upwards [hnear] with s hs
  rw [integral_ornsteinUhlenbeck f hi s hs.le]

end NLAlib
