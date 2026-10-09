import NLAlib.ForMathlib.MeasureTheory.MonotoneDensity
import NLAlib.ForMathlib.MeasureTheory.SmoothMeasureComparison
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Absolute continuity from a weak derivative sign

This file assembles local integral domination and smooth-test measure comparison.
Source: operator rederivations, Section 5, atlas wishart-lambda-min-tail.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal Convolution

namespace NLAlib

/-- The weak derivative sign gives actual domination by a finite multiple of volume
on every smaller positive half-line. Source: operator rederivations, Section 5;
atlas wishart-lambda-min-tail (helper). -/
theorem exists_measure_restrict_le_smul_volume_of_weak_deriv_nonneg
    (μ : Measure ℝ) [μ.Regular] (ℓ a : ℝ) (ha : ℓ < a)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi ℓ → (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, deriv ψ x ∂μ) :
    ∃ C : ℝ≥0, μ.restrict (Ioi a) ≤ C • volume := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_integral_domination_Ioi_of_weak_deriv_nonneg μ ℓ a ha hweak
  refine ⟨Real.toNNReal C, measure_restrict_le_of_integral_contDiff_le μ
    (Real.toNNReal C • volume) isOpen_Ioi ?_⟩
  intro f hf hfc hfs hf0
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Real.coe_toNNReal C hC]
  exact hbound f hf hfc hfs hf0

/-- A positive Radon measure with nonpositive weak derivative is absolutely
continuous on the original open half-line. Absolute continuity is a proved
consequence, not a premise of the density argument.
Source: operator rederivations, Section 5; atlas wishart-lambda-min-tail (helper). -/
theorem measure_restrict_absolutelyContinuous_of_weak_deriv_nonneg
    (μ : Measure ℝ) [μ.Regular] (ℓ : ℝ)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi ℓ → (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, deriv ψ x ∂μ) :
    μ.restrict (Ioi ℓ) ≪ volume := by
  have hac (a : ℝ) (ha : ℓ < a) : μ.restrict (Ioi a) ≪ volume := by
    obtain ⟨C, hC⟩ :=
      exists_measure_restrict_le_smul_volume_of_weak_deriv_nonneg μ ℓ a ha hweak
    exact (Measure.absolutelyContinuous_of_le hC).trans
      (Measure.smul_absolutelyContinuous (μ := volume) (c := (C : ℝ≥0∞)))
  let a : ℕ → ℝ := fun n => ℓ + 1 / ((n : ℝ) + 1)
  have hapos (n : ℕ) : ℓ < a n := by
    dsimp [a]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hcover : Ioi ℓ = ⋃ n, Ioi (a n) := by
    ext x
    simp only [mem_Ioi, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      refine ⟨n, ?_⟩
      dsimp [a]
      linarith
    · rintro ⟨n, hn⟩
      exact (hapos n).trans hn
  intro s hs
  rw [Measure.restrict_apply' measurableSet_Ioi, hcover, inter_iUnion]
  apply measure_iUnion_null
  intro n
  have hzero := hac (a n) (hapos n) hs
  simpa [Measure.restrict_apply' measurableSet_Ioi] using hzero

/-- A locally integrable density satisfying the weak derivative sign has antitone
smooth regularizations on every interior half-line. Source: operator rederivations,
Section 5; atlas wishart-lambda-min-tail (helper). -/
theorem antitoneOn_convolution_of_integral_deriv_mul_nonneg
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (ℓ R : ℝ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρs : tsupport ρ ⊆ Icc (-R) R)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi ℓ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, deriv ψ x * f x) :
    AntitoneOn (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) (Ioi (ℓ + R)) := by
  have hd (x : ℝ) := hρc.hasDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (hρ.of_le (by simp)) hf x
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [interior_Ioi] at hx
  rw [(hd x).deriv]
  have hψ : ContDiff ℝ ∞ (fun y => ρ (x - y)) :=
    hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y => ρ (x - y)) :=
    hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hψs : tsupport (fun y => ρ (x - y)) ⊆ Ioi ℓ := by
    have hh := tsupport_comp_subset_preimage ρ (continuous_const.sub continuous_id :
      Continuous (fun y : ℝ => x - y))
    intro y hy
    have hxy : x - y ∈ Icc (-R) R := hρs (hh hy)
    change ℓ + R < x at hx
    change ℓ < y
    linarith [hxy.2]
  have hw := hweak _ hψ hψc hψs (fun y => hρ0 (x - y))
  have hderiv : ∀ y, deriv (fun z => ρ (x - z)) y = -deriv ρ (x - y) := by
    intro y
    have hh : HasDerivAt (fun z => ρ (x - z)) (-deriv ρ (x - y)) y := by
      convert! (((hρ.differentiable (by simp) (x - y)).hasDerivAt).comp y
        ((hasDerivAt_const y x).sub (hasDerivAt_id y))) using 1
      simp
    exact hh.deriv
  simp_rw [hderiv, neg_mul, integral_neg] at hw
  rw [MeasureTheory.convolution_eq_swap]
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using neg_nonneg.mp hw

/-- A nonnegative locally integrable function with nonpositive weak derivative has
an antitone representative on an open half-line. The representative is obtained
from almost-everywhere convergence of normalized smooth bumps, without assuming
any prior monotonicity of the function. Source: operator rederivations, Section 5;
atlas wishart-lambda-min-tail (helper). -/
theorem exists_antitoneOn_ae_eq_of_integral_deriv_mul_nonneg
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (ℓ : ℝ)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi ℓ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, deriv ψ x * f x) :
    ∃ h : ℝ → ℝ, AntitoneOn h (Ioi ℓ) ∧
      (∀ x ∈ Ioi ℓ, 0 ≤ h x) ∧ h =ᵐ[volume.restrict (Ioi ℓ)] f := by
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    { rIn := 1 / (2 * ((n : ℝ) + 1))
      rOut := 1 / ((n : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hn : 0 < (n : ℝ) + 1 := by positivity
        field_simp
        linarith }
  have hφlim : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ))
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : ∀ n, (φ n).rOut ≤ 2 * (φ n).rIn := by
    intro n
    dsimp [φ]
    field_simp
    linarith
  let F : ℕ → ℝ → ℝ := fun n => (φ n).normed volume ⋆[
    ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  have hFlim : ∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφlim
      (Eventually.of_forall hratio) hf
  have hFanti (n : ℕ) : AntitoneOn (F n) (Ioi (ℓ + (φ n).rOut)) := by
    apply antitoneOn_convolution_of_integral_deriv_mul_nonneg f hf ℓ (φ n).rOut
      ((φ n).normed volume) (φ n).contDiff_normed (φ n).hasCompactSupport_normed
      (φ n).nonneg_normed ?_ hweak
    rw [(φ n).tsupport_normed_eq]
    intro x hx
    simpa only [mem_Icc, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
      abs_le] using hx
  let D : Set ℝ := {x | ℓ < x ∧ Tendsto (fun n => F n x) atTop (𝓝 (f x))}
  have hD : D ⊆ Ioi ℓ := fun _ hx => hx.1
  have hantiD : AntitoneOn f D := by
    intro x hx y hy hxy
    apply le_of_tendsto_of_tendsto_of_frequently hy.2 hx.2
    apply Eventually.frequently
    filter_upwards [(tendsto_order.mp hφlim).2 (x - ℓ) (sub_pos.mpr hx.1),
      (tendsto_order.mp hφlim).2 (y - ℓ) (sub_pos.mpr hy.1)] with n hnx hny
    exact hFanti n (by change ℓ + (φ n).rOut < x; linarith)
      (by change ℓ + (φ n).rOut < y; linarith) hxy
  have hdense : Dense (D ∪ Iic ℓ) := by
    apply volume.dense_of_ae
    filter_upwards [hFlim] with x hx
    by_cases hxl : ℓ < x
    · exact Or.inl ⟨hxl, hx⟩
    · exact Or.inr (le_of_not_gt hxl)
  have hleft : ∀ x ∈ Ioi ℓ, ∃ y ∈ D, y ≤ x := by
    intro x hx
    obtain ⟨y, hy, hyD⟩ := hdense.inter_open_nonempty (Ioo ℓ x) isOpen_Ioo
      (nonempty_Ioo.mpr hx)
    refine ⟨y, ?_, hy.2.le⟩
    rcases hyD with h | h
    · exact h
    · exact False.elim (not_le.mpr hy.1 h)
  have hright : ∀ x ∈ Ioi ℓ, ∃ y ∈ D, x ≤ y := by
    intro x hx
    obtain ⟨y, hy, hyD⟩ := hdense.inter_open_nonempty (Ioo x (x + 1)) isOpen_Ioo
      (nonempty_Ioo.mpr (by linarith))
    refine ⟨y, ?_, hy.1.le⟩
    rcases hyD with h | h
    · exact h
    · exact False.elim (not_le.mpr (hx.trans hy.1) h)
  obtain ⟨h, hh, hh0, heq⟩ := exists_antitoneOn_nonneg_extension_Ioi ℓ D f hD hantiD
    (fun x _ => hf0 x) hleft hright
  refine ⟨h, hh, hh0, ?_⟩
  filter_upwards [ae_restrict_of_ae hFlim, ae_restrict_mem measurableSet_Ioi] with x hx hxl
  exact heq ⟨hxl, hx⟩

/-- A positive Radon measure whose weak derivative is nonpositive has an antitone
nonnegative density on an open half-line. The proof establishes absolute continuity,
constructs the Radon--Nikodym density, and then derives its antitone representative
from normalized smooth convolution. Source: operator rederivations, Section 5;
atlas wishart-lambda-min-tail (helper). -/
theorem exists_antitoneOn_withDensity_eq_of_weak_deriv_nonneg
    (μ : Measure ℝ) [μ.Regular] (ℓ : ℝ)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi ℓ → (∀ x, 0 ≤ ψ x) → 0 ≤ ∫ x, deriv ψ x ∂μ) :
    ∃ h : ℝ → ℝ, AntitoneOn h (Ioi ℓ) ∧ (∀ x ∈ Ioi ℓ, 0 ≤ h x) ∧
      μ.restrict (Ioi ℓ) =
        (volume.restrict (Ioi ℓ)).withDensity (fun x => ENNReal.ofReal (h x)) := by
  let ν : Measure ℝ := μ.restrict (Ioi ℓ)
  have hac : ν ≪ volume :=
    measure_restrict_absolutelyContinuous_of_weak_deriv_nonneg μ ℓ hweak
  let f : ℝ → ℝ := fun x => (ν.rnDeriv volume x).toReal
  have hfloc : LocallyIntegrable f volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    exact Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := volume) hK.measure_lt_top.ne
  have hf0 : ∀ x, 0 ≤ f x := fun _ => ENNReal.toReal_nonneg
  have hfw : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi ℓ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, deriv ψ x * f x := by
    intro ψ hψ hψc hψs hψ0
    have hνψ : (∫ x, deriv ψ x ∂ν) = ∫ x, deriv ψ x ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact deriv_of_notMem_tsupport fun h => hx (hψs h)
    have hRNψ := integral_toReal_rnDeriv_mul (μ := ν) (ν := volume)
      hac (f := deriv ψ)
    have hh : 0 ≤ ∫ x, deriv ψ x ∂ν := by
      rw [hνψ]
      exact hweak ψ hψ hψc hψs hψ0
    rw [← hRNψ] at hh
    simpa [f, mul_comm] using hh
  obtain ⟨h, hh, hh0, heq⟩ :=
    exists_antitoneOn_ae_eq_of_integral_deriv_mul_nonneg f hfloc hf0 ℓ hfw
  refine ⟨h, hh, hh0, ?_⟩
  have hRN : volume.withDensity (ν.rnDeriv volume) = ν :=
    Measure.withDensity_rnDeriv_eq ν volume hac
  have hRNU : (volume.restrict (Ioi ℓ)).withDensity (ν.rnDeriv volume) = ν := by
    rw [← restrict_withDensity measurableSet_Ioi, hRN]
    dsimp [ν]
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_self]
  have hweights : (fun x => ENNReal.ofReal (h x)) =ᵐ[volume.restrict (Ioi ℓ)]
      ν.rnDeriv volume := by
    filter_upwards [heq, ae_restrict_of_ae (Measure.rnDeriv_lt_top ν volume)] with x hx htop
    rw [hx]
    exact ENNReal.ofReal_toReal htop.ne
  exact hRNU.symm.trans (withDensity_congr_ae hweights.symm)

end NLAlib
