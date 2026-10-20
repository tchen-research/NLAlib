import NLAlib.ForMathlib.MeasureTheory.StieltjesFamilyGap
import NLAlib.ForMathlib.MeasureTheory.StieltjesTestGap

/-! # Uniform native sample bounds from an averaged Stieltjes gap

A local averaged O(height) estimate is extended to all heights using
the genuine positive-measure mass bound. A constructed compact positive
test then gives a uniform transform bound on the actual sample support.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Metric
open scoped Topology BoundedContinuousFunction
namespace MeasureTheory

/-- Positive actual sample Stieltjes measures cannot have unbounded
transforms over a real gap of their averaged transform. A local
O(height) estimate suffices: compact tests, almost-everywhere zero
mass, and extension to the true parameter support are all proved.
No measure-valued kernel, pointwise sample gap, or uniform sample
boundary bound is supplied as a hypothesis. -/
theorem exists_uniform_stieltjes_bound_on_support_of_local_average_im_bound
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (ρ : T → FiniteMeasure ℝ) (r : T → ℂ → ℂ)
    (hrep : ∀ t : T, ∀ z : ℂ, 0<z.im → r t z=
      ∫ ξ : ℝ, ((ξ : ℂ)-z)⁻¹ ∂(ρ t : Measure ℝ))
    (hc : ∀ z : ℂ, 0<z.im → Continuous (fun t : T => r t z))
    (B : NNReal) (hmass : ∀ᵐ t ∂ν, (ρ t).mass≤B)
    (hmeas : ∀ γ : NNReal, γ≠0 → AEStronglyMeasurable
      (fun p : T × ℝ => (r p.1 ((p.2 : ℂ)+(γ : ℝ)*Complex.I)).im) (ν.prod volume))
    (x ε δ C : ℝ) (hε : 0<ε) (hδ : 0<δ)
    (havg : ∀ y ∈ ball x ε, ∀ γ : NNReal, γ≠0 → (γ : ℝ)<δ →
      (∫ t : T, (r t ((y : ℂ)+(γ : ℝ)*Complex.I)).im ∂ν)≤C*(γ : ℝ)) :
    ∃ M : ℝ, 0≤M ∧ ∀ t ∈ ν.support, ∀ z : ℂ, 0<z.im → z.re=x → ‖r t z‖≤M := by
  let C0 := max C ((B : ℝ)/δ^2)
  have hfull : ∀ y ∈ ball x ε, ∀ γ : NNReal, γ≠0 →
      (∫ t : T, (r t ((y : ℂ)+(γ : ℝ)*Complex.I)).im ∂ν)≤C0*(γ : ℝ) := by
    intro y hy γ hγ
    have hγpos : 0<(γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
    by_cases hsmall : (γ : ℝ)<δ
    · exact (havg y hy γ hγ hsmall).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hγpos.le)
    · let z : ℂ := (y : ℂ)+(γ : ℝ)*Complex.I
      have hz : 0<z.im := by simpa [z] using hγpos
      have hbound : ∀ᵐ t ∂ν, ‖r t z‖≤(B : ℝ)/(γ : ℝ) := by
        filter_upwards [hmass] with t ht
        rw [hrep t z hz]
        have hh := Complex.norm_integral_real_cauchyKernel_le (ρ t : Measure ℝ) hz
        have hm : (ρ t : Measure ℝ).real univ=((ρ t).mass : ℝ) := by
          rw [Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
        simp only [hm,z,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
          Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero] at hh
        exact hh.trans (div_le_div_of_nonneg_right (NNReal.coe_le_coe.mpr ht) hγpos.le)
      have hi : Integrable (fun t : T => r t z) ν :=
        (integrable_const _).mono' (hc z hz).aestronglyMeasurable hbound
      have hmean : (∫ t : T, (r t z).im ∂ν)≤(B : ℝ)/(γ : ℝ) := by
        calc
          _ ≤ ∫ _t : T, (B : ℝ)/(γ : ℝ) ∂ν :=
            integral_mono_ae hi.im (integrable_const _)
              (hbound.mono fun t ht => (Complex.im_le_norm _).trans ht)
          _ = _ := by simp only [integral_const,probReal_univ,one_smul]
      have hδγ : δ≤(γ : ℝ) := le_of_not_gt hsmall
      have hsq : δ^2≤(γ : ℝ)^2 := pow_le_pow_left₀ hδ.le hδγ 2
      have hlarge : (B : ℝ)/(γ : ℝ)≤((B : ℝ)/δ^2)*(γ : ℝ) := by
        calc
          _ = ((B : ℝ)*(γ : ℝ))/(γ : ℝ)^2 := by field_simp [hγpos.ne']
          _ ≤ ((B : ℝ)*(γ : ℝ))/δ^2 :=
            div_le_div_of_nonneg_left (mul_nonneg B.property hγpos.le) (sq_pos_of_pos hδ) hsq
          _ = _ := by ring
      exact hmean.trans (hlarge.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hγpos.le))
  let a := ε/2
  have ha : 0<a := half_pos hε
  have haε : a<ε := by dsimp only [a]; linarith
  obtain ⟨g,hgone,hgzero,hgcompact,hgrange⟩ :=
    exists_continuous_one_zero_of_isCompact (isCompact_closedBall x a)
      isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (closedBall_subset_ball haε))
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g g.continuous 1
    (fun y => by rw [Real.norm_of_nonneg (hgrange y).1]; exact (hgrange y).2)
  have hfint : Integrable f := g.continuous.integrable_of_hasCompactSupport hgcompact
  have hfnonneg : ∀ y : ℝ, 0≤f y := fun y => (hgrange y).1
  have hfone : ∀ y : ℝ, |y-x|<a → 1≤f y := by
    intro y hy
    have hymem : y∈closedBall x a := by simpa only [mem_closedBall,Real.dist_eq] using hy.le
    exact (hgone hymem).symm.le
  have hzero := ae_integral_eq_zero_of_average_im_stieltjes_le_mul ν ρ r hrep B hmass hmeas
    f hfint hfnonneg (ball x ε) (fun y hy => hgzero hy) C0 hfull
  refine ⟨a⁻¹*(B : ℝ),by positivity,?_⟩
  intro t ht z hz hzx
  exact norm_stieltjes_family_le_on_support_of_ae_zero_positive_test ν ρ r hrep hc B hmass
    f hfnonneg hzero x a ha hfone t ht z hz hzx

end MeasureTheory
