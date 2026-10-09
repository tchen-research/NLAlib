import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrating factors and monotone regularizations

This file supplies calculus prerequisites for the scalar weighted-density argument
in Section 5 of Re-derivations/operator_rederivations.tex, atlas
wishart-lambda-min-tail. The resulting density theorem is proved in WeakDensity
and LocalWeakDensity; the Gamma-weighted application is in WeightedWeakDensity.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace NLAlib

/-- The derivative of a power times an exponential, expressed using its logarithmic
derivative. Source: operator rederivations, Section 5 (integrating factor);
atlas wishart-lambda-min-tail (helper). -/
theorem hasDerivAt_rpow_mul_exp (a b x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ a * Real.exp (b * y))
      ((a / x + b) * (x ^ a * Real.exp (b * x))) x := by
  have hp := Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')
  have he := ((hasDerivAt_id x).const_mul b).exp
  convert! hp.mul he using 1
  simp only [id_eq, mul_one]
  rw [Real.rpow_sub_one hx.ne' a]
  field_simp

/-- Multiplication by the Gamma integrating factor cancels the zeroth-order
coefficient of the scalar Wishart weak inequality. Source: operator rederivations,
Section 5, the weighted-density substitution; atlas wishart-lambda-min-tail
(helper). -/
theorem weighted_deriv_mul_rpow_exp_eq (m x : ℝ) (hx : 0 < x)
    (η : ℝ → ℝ) (hη : DifferentiableAt ℝ η x) :
    4 * x * deriv (fun y => η y * (y ^ (-m / 2) * Real.exp (y / 2))) x +
        2 * (m - x) * (η x * (x ^ (-m / 2) * Real.exp (x / 2))) =
      4 * (x ^ (1 - m / 2) * Real.exp (x / 2)) * deriv η x := by
  have hg := hasDerivAt_rpow_mul_exp (-m / 2) (1 / 2) x hx
  have heq : (fun y : ℝ => y ^ (-m / 2) * Real.exp (1 / 2 * y)) =
      (fun y : ℝ => y ^ (-m / 2) * Real.exp (y / 2)) := by
    funext y
    congr 2
    ring
  rw [heq] at hg
  have hbx : (1 : ℝ) / 2 * x = x / 2 := by ring
  rw [hbx] at hg
  have hd : deriv (fun y => η y * (y ^ (-m / 2) * Real.exp (y / 2))) x =
      deriv η x * (x ^ (-m / 2) * Real.exp (x / 2)) +
        η x * ((-m / 2 / x + 1 / 2) * (x ^ (-m / 2) * Real.exp (x / 2))) :=
    (hη.hasDerivAt.mul hg).deriv
  rw [hd]
  have hp : x ^ (1 - m / 2) = x * x ^ (-m / 2) := by
    rw [show 1 - m / 2 = 1 + (-m / 2) by ring, Real.rpow_add hx, Real.rpow_one]
  rw [hp]
  field_simp
  ring

/-- A multiplier smooth on an open neighborhood of the support preserves global
smoothness. This is the support-localization needed for the Gamma integrating factor.
Source: operator rederivations, Section 5; atlas wishart-lambda-min-tail (helper). -/
theorem contDiff_mul_of_tsupport_subset {n : WithTop ℕ∞} {η g : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hη : ContDiff ℝ n η)
    (hg : ContDiffOn ℝ n g U) (hsub : tsupport η ⊆ U) :
    ContDiff ℝ n (fun x => η x * g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport η
  · exact hη.contDiffAt.mul ((hg x (hsub hx)).contDiffAt (hU.mem_nhds (hsub hx)))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

/-- The Gamma integrating factor transfers the weak scalar Wishart inequality to
the weak sign condition for a density divided by its Gamma weight. The original
hypothesis is tested only against smooth nonnegative functions compactly supported
in the positive half-line. Source: operator rederivations, Section 5;
atlas wishart-lambda-min-tail (helper). -/
theorem integral_rpow_exp_mul_deriv_nonneg_of_weak_gamma
    (μ : Measure ℝ) (m : ℝ)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi 0 → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x in Ioi 0, 4 * x * deriv ψ x + 2 * (m - x) * ψ x ∂μ)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ioi 0) (hη0 : ∀ x, 0 ≤ η x) :
    0 ≤ ∫ x in Ioi 0,
      (x ^ (1 - m / 2) * Real.exp (x / 2)) * deriv η x ∂μ := by
  let g : ℝ → ℝ := fun x => x ^ (-m / 2) * Real.exp (x / 2)
  have hg : ContDiffOn ℝ ∞ g (Ioi 0) := by
    intro x hx
    exact ((Real.contDiffAt_rpow_const_of_ne (p := -m / 2) (ne_of_gt hx)).mul
      ((contDiffAt_id.div_const 2).exp)).contDiffWithinAt
  have hψ := contDiff_mul_of_tsupport_subset isOpen_Ioi hη hg hηs
  have hψc : HasCompactSupport (fun x => η x * g x) := hηc.mul_right
  have hψs : tsupport (fun x => η x * g x) ⊆ Ioi 0 :=
    tsupport_mul_subset_left.trans hηs
  have hψ0 : ∀ x, 0 ≤ η x * g x := by
    intro x
    by_cases hx : 0 < x
    · exact mul_nonneg (hη0 x) (mul_nonneg (Real.rpow_nonneg hx.le _)
        (Real.exp_nonneg _))
    · have hn : x ∉ tsupport η := fun h => hx (hηs h)
      simp [image_eq_zero_of_notMem_tsupport hn]
  have hw := hweak _ hψ hψc hψs hψ0
  have heq :
      (∫ x in Ioi 0, 4 * x * deriv (fun y => η y * g y) x +
          2 * (m - x) * (η x * g x) ∂μ) =
      4 * ∫ x in Ioi 0,
        (x ^ (1 - m / 2) * Real.exp (x / 2)) * deriv η x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa [g, mul_assoc] using weighted_deriv_mul_rpow_exp_eq m x hx η
      (hη.differentiable (by simp) x)
  rw [heq] at hw
  linarith

/-- A bounded differentiable kernel can be differentiated after averaging it against
a finite measure. Source: operator rederivations, Section 5, mollification step;
atlas wishart-lambda-min-tail (helper). -/
theorem hasDerivAt_integral_sub_kernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ) (x : ℝ) :
    HasDerivAt (fun z => ∫ y, ρ (z - y) ∂μ) (∫ y, deriv ρ (x - y) ∂μ) x := by
  obtain ⟨C, hC⟩ := (hρ.continuous_deriv le_rfl).bounded_above_of_compact_support
    hρc.deriv
  have hcont (z : ℝ) : Continuous (fun y => ρ (z - y)) :=
    hρ.continuous.comp (continuous_const.sub continuous_id)
  have hdcont (z : ℝ) : Continuous (fun y => deriv ρ (z - y)) :=
    (hρ.continuous_deriv le_rfl).comp (continuous_const.sub continuous_id)
  have hi : Integrable (fun y => ρ (x - y)) μ := by
    obtain ⟨B, hB⟩ := hρ.continuous.bounded_above_of_compact_support hρc
    exact (integrable_const B).mono' (hcont x).aestronglyMeasurable
      (Eventually.of_forall fun y => hB (x - y))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (bound := fun _ => C) (F := fun z y => ρ (z - y))
    (F' := fun z y => deriv ρ (z - y)) (by simp)
    (Eventually.of_forall fun z => (hcont z).aestronglyMeasurable) hi
    (hdcont x).aestronglyMeasurable
    (Eventually.of_forall fun y z _ => hC (z - y)) (integrable_const C) ?_).2
  filter_upwards with y
  intro z _
  convert! ((hρ.differentiable (by norm_num) (z - y)).hasDerivAt.comp z
    ((hasDerivAt_id z).sub_const y)) using 1
  simp

/-- A nonnegative smooth compactly supported kernel regularizes a positive measure
with nonpositive weak derivative to an antitone function on every interior interval.
The weak hypothesis is tested against all smooth nonnegative functions supported in
the original interval. Source: operator rederivations, Section 5, mollification step;
atlas wishart-lambda-min-tail (helper). -/
theorem antitoneOn_integral_sub_of_integral_deriv_nonneg
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a b R : ℝ) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hsupp : tsupport ρ ⊆ Icc (-R) R)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∀ y, 0 ≤ ψ y) →
      0 ≤ ∫ y, deriv ψ y ∂μ) :
    AntitoneOn (fun x => ∫ y, ρ (x - y) ∂μ) (Ioo (a + R) (b - R)) := by
  have hd (x : ℝ) := hasDerivAt_integral_sub_kernel μ ρ (hρ.of_le (by simp)) hρc x
  apply antitoneOn_of_deriv_nonpos (convex_Ioo _ _)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [interior_Ioo] at hx
  rw [(hd x).deriv]
  have hψ : ContDiff ℝ ∞ (fun y => ρ (x - y)) :=
    hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y => ρ (x - y)) :=
    hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hψs : tsupport (fun y => ρ (x - y)) ⊆ Ioo a b := by
    have hh := tsupport_comp_subset_preimage ρ (continuous_const.sub continuous_id :
      Continuous (fun y : ℝ => x - y))
    intro y hy
    have hxy : x - y ∈ Icc (-R) R := hsupp (hh hy)
    constructor <;> linarith [hx.1, hx.2, hxy.1, hxy.2]
  have hw := hweak _ hψ hψc hψs (fun y => hρ0 (x - y))
  have hderiv : ∀ y, deriv (fun z => ρ (x - z)) y = -deriv ρ (x - y) := by
    intro y
    have hh : HasDerivAt (fun z => ρ (x - z)) (-deriv ρ (x - y)) y := by
      convert! (((hρ.differentiable (by simp) (x - y)).hasDerivAt).comp y
        ((hasDerivAt_const y x).sub (hasDerivAt_id y))) using 1
      simp
    exact hh.deriv
  simp_rw [hderiv, integral_neg] at hw
  linarith

/-- Two nonnegative smooth functions with disjoint ordered supports and equal total
mass admit a nonnegative smooth compactly supported primitive of their difference.
This turns a weak derivative inequality into local integral domination.
Source: operator rederivations, Section 5, interval alternative to mollification;
atlas wishart-lambda-min-tail (helper). -/
theorem exists_nonneg_primitive_of_ordered_supports
    (c a b : ℝ) (hca : c < a) (hab : a < b)
    (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfs : tsupport f ⊆ Ioo a b) (hgs : tsupport g ⊆ Ioo c a)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hmass : ∫ x, f x = ∫ x, g x) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Icc c b ∧ (∀ x, 0 ≤ φ x) ∧
      ∀ x, deriv φ x = g x - f x := by
  have hfi : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport hfc
  have hgi : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hgc
  let q : ℝ → ℝ := fun x => g x - f x
  let φ : ℝ → ℝ := fun x => ∫ y in Iic x, q y
  have hqi : Integrable q volume := hgi.sub hfi
  have hqc : ContDiff ℝ ∞ q := hg.sub hf
  have hφd (x : ℝ) : HasDerivAt φ (q x) x := by
    have hh := intervalIntegral.integral_hasDerivAt_right
      (hqc.continuous.intervalIntegrable c x)
      hqc.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      hqc.continuous.continuousAt
    have heq : φ = fun z => (∫ y in c..z, q y) + ∫ y in Iic c, q y := by
      funext z
      have hz := intervalIntegral.integral_Iic_sub_Iic hqi.integrableOn hqi.integrableOn
        (a := c) (b := z)
      dsimp [φ]
      linarith
    rw [heq]
    exact hh.add_const _
  have hφsmooth : ContDiff ℝ ∞ φ := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (hφd x).differentiableAt, ?_⟩
    have heq : deriv φ = q := funext fun x => (hφd x).deriv
    rw [heq]
    exact hqc
  have hφsplit (x : ℝ) :
      φ x = (∫ y in Iic x, g y) - ∫ y in Iic x, f y := by
    exact integral_sub hgi.integrableOn hfi.integrableOn
  have hleft (x : ℝ) (hx : x ≤ c) : φ x = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    change y ≤ x at hy
    have hgy : g y = 0 := image_eq_zero_of_notMem_tsupport fun h => by
      have := (hgs h).1
      linarith
    have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport fun h => by
      have := (hfs h).1
      linarith
    simp [q, hgy, hfy]
  have hright (x : ℝ) (hx : b ≤ x) : φ x = 0 := by
    have hfull : (∫ y in Iic x, q y) = ∫ y, q y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport fun h => by
        have := (hfs h).2
        simp only [mem_Iic, not_le] at hy
        linarith
      have hgy : g y = 0 := image_eq_zero_of_notMem_tsupport fun h => by
        have := (hgs h).2
        simp only [mem_Iic, not_le] at hy
        linarith
      simp [q, hgy, hfy]
    dsimp [φ]
    rw [hfull, integral_sub hgi hfi, hmass, sub_self]
  have hsupp : tsupport φ ⊆ Icc c b := by
    apply closure_minimal ?_ isClosed_Icc
    intro x hx
    constructor
    · by_contra h
      exact hx (hleft x (le_of_not_ge h))
    · by_contra h
      exact hx (hright x (le_of_not_ge h))
  refine ⟨φ, hφsmooth, HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport φ).trans hsupp), hsupp, ?_, fun x => (hφd x).deriv⟩
  intro x
  rw [hφsplit]
  by_cases hx : x ≤ a
  · have hz : (∫ y in Iic x, f y) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      change y ≤ x at hy
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have := (hfs h).1
      linarith
    rw [hz, sub_zero]
    exact integral_nonneg fun y => hg0 y
  · have hfull : (∫ y in Iic x, g y) = ∫ y, g y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have := (hgs h).2
      simp only [mem_Iic, not_le] at hy
      linarith
    rw [hfull, ← hmass]
    exact sub_nonneg.mpr (setIntegral_le_integral hfi (Eventually.of_forall hf0))

/-- The weak derivative sign controls any nonnegative smooth test on a right
interval by its Lebesgue integral and one fixed normalized test to its left.
This is a genuine local domination consequence and does not assume a density.
Source: operator rederivations, Section 5, interval alternative to mollification;
atlas wishart-lambda-min-tail (helper). -/
theorem integral_le_integral_mul_of_weak_deriv_nonneg
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (ℓ c a b : ℝ) (hc : ℓ < c) (hca : c < a) (hab : a < b)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi ℓ → (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, deriv ψ x ∂μ)
    (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfs : tsupport f ⊆ Ioo a b) (hgs : tsupport g ⊆ Ioo c a)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hgmass : ∫ x, g x = 1) :
    (∫ x, f x ∂μ) ≤ (∫ x, f x) * ∫ x, g x ∂μ := by
  let J : ℝ := ∫ x, f x
  have hJ : 0 ≤ J := integral_nonneg hf0
  have hg' : ContDiff ℝ ∞ (fun x => J * g x) := contDiff_const.mul hg
  have hgc' : HasCompactSupport (fun x => J * g x) := hgc.mul_left
  have hgs' : tsupport (fun x => J * g x) ⊆ Ioo c a :=
    tsupport_mul_subset_right.trans hgs
  have hm : (∫ x, f x) = ∫ x, J * g x := by
    rw [integral_const_mul, hgmass, mul_one]
  obtain ⟨φ, hφ, hφc, hφs, hφ0, hφd⟩ :=
    exists_nonneg_primitive_of_ordered_supports c a b hca hab f (fun x => J * g x)
      hf hg' hfc hgc' hfs hgs' hf0 (fun x => mul_nonneg hJ (hg0 x)) hm
  have hφpos : tsupport φ ⊆ Ioi ℓ := fun x hx =>
    hc.trans_le (hφs hx).1
  have hw := hweak φ hφ hφc hφpos hφ0
  simp_rw [hφd] at hw
  rw [integral_sub (hg'.continuous.integrable_of_hasCompactSupport hgc')
    (hf.continuous.integrable_of_hasCompactSupport hfc), integral_const_mul] at hw
  exact sub_nonneg.mp hw

/-- A nonempty real interval contains a nonnegative smooth compactly supported
function of Lebesgue integral one. Source: operator rederivations, Section 5,
local integral domination; atlas wishart-lambda-min-tail (helper). -/
theorem exists_contDiff_nonneg_integral_eq_one_tsupport_Ioo
    (a b : ℝ) (hab : a < b) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ioo a b ∧ (∀ x, 0 ≤ g x) ∧ ∫ x, g x = 1 := by
  let φ : ContDiffBump ((a + b) / 2) :=
    { rIn := (b - a) / 8
      rOut := (b - a) / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨φ.normed volume, φ.contDiff_normed, φ.hasCompactSupport_normed, ?_,
    φ.nonneg_normed, φ.integral_normed⟩
  rw [φ.tsupport_normed_eq]
  intro x hx
  simp only [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  change -(φ.rOut) ≤ x - (a + b) / 2 ∧ x - (a + b) / 2 ≤ φ.rOut at hx
  dsimp [φ] at hx
  constructor <;> linarith [hx.1, hx.2]

/-- A positive locally finite measure with nonpositive weak derivative has a
uniform integral domination bound to the right of every interior point. The
constant is finite because it is the integral of one fixed compactly supported
test. Source: operator rederivations, Section 5, interval alternative;
atlas wishart-lambda-min-tail (helper). -/
theorem exists_integral_domination_Ioi_of_weak_deriv_nonneg
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] (ℓ a : ℝ) (ha : ℓ < a)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi ℓ → (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, deriv ψ x ∂μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioi a → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C * ∫ x, f x := by
  let c : ℝ := (ℓ + a) / 2
  have hc : ℓ < c := by dsimp [c]; linarith
  have hca : c < a := by dsimp [c]; linarith
  obtain ⟨g, hg, hgc, hgs, hg0, hgmass⟩ :=
    exists_contDiff_nonneg_integral_eq_one_tsupport_Ioo c a hca
  refine ⟨∫ x, g x ∂μ, integral_nonneg hg0, ?_⟩
  intro f hf hfc hfs hf0
  obtain ⟨B, hB⟩ := hfc.isCompact.bddAbove
  let b : ℝ := max B a + 1
  have hab : a < b := by dsimp [b]; linarith [le_max_right B a]
  have hfb : tsupport f ⊆ Ioo a b := by
    intro x hx
    refine ⟨hfs hx, ?_⟩
    have hxb : x ≤ B := hB hx
    dsimp [b]
    linarith [le_max_left B a]
  simpa [mul_comm] using integral_le_integral_mul_of_weak_deriv_nonneg μ ℓ c a b
    hc hca hab hweak f g hf hg hfc hgc hfb hgs hf0 hg0 hgmass

/-- A nonnegative antitone function on an order-dense subset of a half-line admits
an antitone nonnegative representative on the whole half-line. Density is supplied
as explicit left and right witnesses, which can be obtained from an almost-everywhere
set. Source: operator rederivations, Section 5, monotone density representative;
atlas wishart-lambda-min-tail (helper). -/
theorem exists_antitoneOn_nonneg_extension_Ioi
    (ℓ : ℝ) (D : Set ℝ) (f : ℝ → ℝ) (hD : D ⊆ Ioi ℓ)
    (hf : AntitoneOn f D) (hf0 : ∀ x ∈ D, 0 ≤ f x)
    (hleft : ∀ x ∈ Ioi ℓ, ∃ y ∈ D, y ≤ x)
    (hright : ∀ x ∈ Ioi ℓ, ∃ y ∈ D, x ≤ y) :
    ∃ h : ℝ → ℝ, AntitoneOn h (Ioi ℓ) ∧ (∀ x ∈ Ioi ℓ, 0 ≤ h x) ∧ EqOn h f D := by
  let S : ℝ → Set ℝ := fun x => f '' (D ∩ Ici x)
  have hSnonempty (x : ℝ) (hx : x ∈ Ioi ℓ) : (S x).Nonempty := by
    obtain ⟨y, hy, hxy⟩ := hright x hx
    exact ⟨f y, ⟨y, ⟨hy, hxy⟩, rfl⟩⟩
  have hSbdd (x : ℝ) (hx : x ∈ Ioi ℓ) : BddAbove (S x) := by
    obtain ⟨y, hy, hyx⟩ := hleft x hx
    refine ⟨f y, ?_⟩
    rintro _ ⟨z, ⟨hz, hxz⟩, rfl⟩
    exact hf hy hz (hyx.trans hxz)
  refine ⟨fun x => sSup (S x), ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    apply csSup_le_csSup (hSbdd x hx) (hSnonempty y hy)
    exact image_mono fun z hz => ⟨hz.1, hxy.trans hz.2⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hright x hx
    exact (hf0 y hy).trans (le_csSup (hSbdd x hx) ⟨y, ⟨hy, hxy⟩, rfl⟩)
  · intro x hx
    apply le_antisymm
    · apply csSup_le (hSnonempty x (hD hx))
      rintro _ ⟨z, ⟨hz, hxz⟩, rfl⟩
      exact hf hx hz hxz
    · exact le_csSup (hSbdd x (hD hx)) ⟨x, ⟨hx, by simp⟩, rfl⟩

end NLAlib
