import NLAlib.ForMathlib.Analysis.Complex.CurveLogPrimitive
import NLAlib.ForMathlib.Analysis.Complex.CubicalCauchyFormula
import NLAlib.ForMathlib.Analysis.Complex.CubicalIntegralAlgebra
import NLAlib.ForMathlib.Analysis.Complex.CubicalTrace
import NLAlib.ForMathlib.Analysis.Complex.CubicalIntegralBounds
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Local constancy and exterior vanishing of finite-chain winding

Finite signed C1 contours use their native endpoint cycle condition.
Log-quotient primitives and finite boundary cancellation prove local
constancy, while actual length bounds prove vanishing on unbounded
complement components. Corners and stationary derivatives are retained.
Atlas: `gauss-remainder-contour-kernel`, analytic prerequisites only.
-/

noncomputable section
open Set Finset Filter MeasureTheory
open scoped unitInterval Topology
namespace Complex

/-- An actual primitive integrates to zero on every finite smooth cycle.
The native endpoint boundary cancels all endpoint terms, including corners. -/
theorem cubicalCurveIntegral_eq_zero_of_primitive {Ω U : Set ℂ}
    (Γ : Cubical.OneChain Ω) (hc : Cubical.boundaryOne Γ = 0)
    {G g : ℂ → ℂ}
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z) (hg : ContinuousOn g U)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hΓU : ∀ γ ∈ Γ.support, ∀ t, (γ t : ℂ) ∈ U) :
    cubicalCurveIntegral g Γ = 0 := by
  let L : (Ω →₀ ℤ) →ₗ[ℤ] ℂ := Finsupp.linearCombination ℤ (fun z : Ω => G z)
  have he : cubicalCurveIntegral g Γ = L (Cubical.boundaryOne Γ) := by
    unfold cubicalCurveIntegral Cubical.boundaryOne
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
    apply sum_congr rfl
    intro γ hγ
    rw [curveIntegral_eq_sub_of_hasDerivAt (cubicalPath γ) hG hg (hΓ γ hγ) (hΓU γ hγ)]
    simp [L]
  rw [he, hc, map_zero]

/-- Nearby avoided targets have exactly equal actual winding integrals
on a finite smooth cycle, by a constructed log primitive and endpoint cancellation. -/
theorem cubicalWindingIntegral_eq_of_norm_sub_lt {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) (hc : Cubical.boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {u v : ℂ} (hnear : ∀ γ ∈ Γ.support, ∀ t, ‖u - v‖ < ‖(γ t : ℂ) - u‖) :
    cubicalWindingIntegral Γ v = cubicalWindingIntegral Γ u := by
  let U : Set ℂ := {z | ‖u - v‖ < ‖z - u‖}
  have hu : ContinuousOn (fun z => (z - u)⁻¹) U :=
    (continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz => (sub_ne_zero_and_sub_ne_zero_of_norm_sub_lt hz).1)
  have hv : ContinuousOn (fun z => (z - v)⁻¹) U :=
    (continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz => (sub_ne_zero_and_sub_ne_zero_of_norm_sub_lt hz).2)
  have hz := cubicalCurveIntegral_eq_zero_of_primitive Γ hc
    (fun z hz => hasDerivAt_log_div_sub_of_norm_sub_lt hz) (hv.sub hu) hΓ hnear
  have hi (w : ℂ) (hw : ∀ z ∈ U, z - w ≠ 0) :
      ∀ γ ∈ Γ.support, CurveIntegrable
        (fun z => (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ) := by
    intro γ hγ
    apply (((continuousOn_id.sub continuousOn_const).inv₀ hw).smul continuousOn_const).curveIntegrable_of_contDiffOn
      (hΓ γ hγ) (fun t => hnear γ hγ t)
  rw [cubicalCurveIntegral_sub Γ _ _
    (hi v (fun z hz => (sub_ne_zero_and_sub_ne_zero_of_norm_sub_lt hz).2))
    (hi u (fun z hz => (sub_ne_zero_and_sub_ne_zero_of_norm_sub_lt hz).1)), sub_eq_zero] at hz
  unfold cubicalWindingIntegral
  rw [hz]

/-- The actual winding integral is constant on a target neighborhood
disjoint from the compact contour trace. -/
theorem eventually_cubicalWindingIntegral_eq {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) (hc : Cubical.boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {u : ℂ} (hu : u ∉ cubicalTrace Γ) :
    ∀ᶠ v in 𝓝 u, cubicalWindingIntegral Γ v = cubicalWindingIntegral Γ u := by
  have hop : IsOpen ((cubicalTrace Γ)ᶜ) := (isCompact_cubicalTrace Γ).isClosed.isOpen_compl
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hop.mem_nhds hu)
  filter_upwards [Metric.ball_mem_nhds u hε] with v hv
  apply cubicalWindingIntegral_eq_of_norm_sub_lt Γ hc hΓ
  intro γ hγ r
  have hnot : (γ r : ℂ) ∉ Metric.ball u ε :=
    fun hr => (hsub hr) (mem_cubicalTrace hγ r)
  have hlower : ε ≤ ‖(γ r : ℂ) - u‖ := by
    exact le_of_not_gt (by simpa only [Metric.mem_ball, dist_eq_norm] using hnot)
  have hdist : ‖u - v‖ < ε := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hv
  exact hdist.trans_le hlower

/-- The actual winding integral is locally constant on the entire
trace complement. No classification or integer-valued winding premise is assumed.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem isLocallyConstant_cubicalWindingIntegral {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) (hc : Cubical.boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I) :
    IsLocallyConstant (fun u : {z : ℂ // z ∉ cubicalTrace Γ} => cubicalWindingIntegral Γ u) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro u
  exact continuous_subtype_val.continuousAt.tendsto.eventually
    (eventually_cubicalWindingIntegral_eq Γ hc hΓ u.property)

/-- Actual contour length bounds winding at distant targets by
length/(2*pi) divided by the distance from a containing ball. -/
theorem norm_cubicalWindingIntegral_le_div_of_trace_bound {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {R : ℝ} (hR : ∀ z ∈ cubicalTrace Γ, ‖z‖ ≤ R)
    {v : ℂ} (hv : R < ‖v‖) :
    ‖cubicalWindingIntegral Γ v‖ ≤
      (cubicalLength Γ / (2 * Real.pi)) / (‖v‖ - R) := by
  have hδ : 0 < ‖v‖ - R := sub_pos.mpr hv
  have hb := norm_two_pi_i_inv_mul_cubicalCurveIntegral_le_length_mul Γ
    (fun z => (z - v)⁻¹) (C := (‖v‖ - R)⁻¹) hΓ (by
    intro γ hγ t
    have hrev := norm_sub_norm_le v (γ t : ℂ)
    rw [norm_sub_rev] at hrev
    have hl : ‖v‖ - R ≤ ‖(γ t : ℂ) - v‖ := by
      linarith [hR (γ t) (mem_cubicalTrace hγ t)]
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hδ hl)
  simpa only [cubicalWindingIntegral, div_eq_mul_inv] using hb

/-- Every nonzero winding level set is bounded, directly from
the actual contour-length estimate; a cycle assumption is unnecessary. -/
theorem isBounded_cubicalWindingIntegral_level_of_ne_zero {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {w : ℂ} (hw : w ≠ 0) : Bornology.IsBounded {v : ℂ | cubicalWindingIntegral Γ v = w} := by
  obtain ⟨R, hRpos, hR⟩ := (isCompact_cubicalTrace Γ).isBounded.exists_pos_norm_le
  let L : ℝ := cubicalLength Γ / (2 * Real.pi)
  have hL : 0 ≤ L := div_nonneg (cubicalLength_nonneg Γ) (by positivity)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R + L / ‖w‖ + 1, ?_⟩
  intro v hv
  by_contra hnot
  have hbig : R + L / ‖w‖ + 1 < ‖v‖ := lt_of_not_ge hnot
  have hdiv : 0 ≤ L / ‖w‖ := div_nonneg hL hwpos.le
  have hfar : R < ‖v‖ := by linarith
  have hb := norm_cubicalWindingIntegral_le_div_of_trace_bound Γ hΓ hR hfar
  rw [show cubicalWindingIntegral Γ v = w from hv] at hb
  have hmul := (le_div_iff₀ (sub_pos.mpr hfar)).mp hb
  have hstrict : L < (‖v‖ - R) * ‖w‖ :=
    (div_lt_iff₀ hwpos).mp (by linarith : L / ‖w‖ < ‖v‖ - R)
  change ‖w‖ * (‖v‖ - R) ≤ L at hmul
  nlinarith

/-- Winding vanishes on every unbounded preconnected subset of
the trace complement, by local constancy and bounded nonzero level sets. -/
theorem cubicalWindingIntegral_eq_zero_of_unbounded_preconnected {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) (hc : Cubical.boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {S : Set ℂ} (hs : IsPreconnected S) (hoff : S ⊆ (cubicalTrace Γ)ᶜ)
    (hunbounded : ¬ Bornology.IsBounded S) {u : ℂ} (hu : u ∈ S) :
    cubicalWindingIntegral Γ u = 0 := by
  let : PreconnectedSpace S := Subtype.preconnectedSpace hs
  have hloc := (isLocallyConstant_cubicalWindingIntegral Γ hc hΓ).comp_continuous
    (show Continuous (fun v : S => (⟨v, hoff v.property⟩ : {z : ℂ // z ∉ cubicalTrace Γ}))
      from continuous_subtype_val.subtype_mk _)
  by_contra hne
  apply hunbounded
  apply (isBounded_cubicalWindingIntegral_level_of_ne_zero Γ hΓ hne).subset
  intro v hv
  exact hloc.apply_eq_of_preconnectedSpace ⟨v, hv⟩ ⟨u, hu⟩

/-- Actual winding vanishes on each unbounded complementary
component, with no Jordan separation or homotopy premise.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem cubicalWindingIntegral_eq_zero_of_unbounded_component {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) (hc : Cubical.boundaryOne Γ = 0)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    {u : ℂ} (hu : u ∉ cubicalTrace Γ)
    (hunbounded : ¬ Bornology.IsBounded (connectedComponentIn (cubicalTrace Γ)ᶜ u)) :
    cubicalWindingIntegral Γ u = 0 :=
  cubicalWindingIntegral_eq_zero_of_unbounded_preconnected Γ hc hΓ
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) hunbounded
    (mem_connectedComponentIn hu)

end Complex
