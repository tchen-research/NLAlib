import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Analysis.Analytic.Constructions

/-!
# Analytic dependence of fixed circle integrals

Integration on a fixed circle is a continuous complex-linear functional on
continuous functions on that circle. Banach-algebra inversion then proves
analytic dependence of contour quotients without choosing individual roots.
This supports the root-cluster argument for `trace-exponential-stahl`.
-/

noncomputable section

open Complex Metric Set Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace circleIntegral

private def extendFromSphere {c : ℂ} {r : ℝ} (f : C(sphere c r, ℂ)) (z : ℂ) : ℂ :=
  if hz : z ∈ sphere c r then f ⟨z, hz⟩ else 0

private theorem continuousOn_extendFromSphere {c : ℂ} {r : ℝ}
    (f : C(sphere c r, ℂ)) : ContinuousOn (extendFromSphere f) (sphere c r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.continuous using 1
  ext z
  change extendFromSphere f z = f z
  simp only [extendFromSphere, dif_pos z.property]

/-- Integration along a fixed counterclockwise circle is a continuous complex-linear
functional on its continuous functions. -/
def continuousMapIntegral (c : ℂ) (r : ℝ) (hr : 0 ≤ r) : C(sphere c r, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∮ z in C(c, r), extendFromSphere f z
      map_add' := by
        intro f g
        have heq : extendFromSphere (f + g) =
            fun z => extendFromSphere f z + extendFromSphere g z := by
          ext z
          by_cases hz : z ∈ sphere c r
          · simp only [extendFromSphere, dif_pos hz, ContinuousMap.add_apply]
          · simp only [extendFromSphere, dif_neg hz, add_zero]
        rw [heq]
        exact integral_add ((continuousOn_extendFromSphere f).circleIntegrable hr)
          ((continuousOn_extendFromSphere g).circleIntegrable hr)
      map_smul' := by
        intro a f
        have heq : extendFromSphere (a • f) = fun z => a • extendFromSphere f z := by
          ext z
          by_cases hz : z ∈ sphere c r
          · simp only [extendFromSphere, dif_pos hz, ContinuousMap.smul_apply]
          · simp only [extendFromSphere, dif_neg hz, smul_zero]
        rw [heq]
        exact integral_smul a (extendFromSphere f) c r }
    (2 * Real.pi * r) fun f =>
      norm_integral_le_of_norm_le_const hr fun z hz => by
        simpa only [extendFromSphere, dif_pos hz] using f.norm_coe_le_norm ⟨z, hz⟩

/-- The continuous linear circle integral agrees with the ordinary circle integral
of any function whose restriction supplies the bundled continuous map. -/
theorem continuousMapIntegral_eq {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (f : C(sphere c r, ℂ)) (g : ℂ → ℂ)
    (hg : ∀ z (hz : z ∈ sphere c r), f ⟨z, hz⟩ = g z) :
    continuousMapIntegral c r hr f = ∮ z in C(c, r), g z := by
  apply integral_congr hr
  intro z hz
  simpa only [extendFromSphere, dif_pos hz] using hg z hz

private theorem inverse_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) (hf : IsUnit f) (x : X) :
    (Ring.inverse f) x = (f x)⁻¹ := by
  have hmul := congrArg (fun g : C(X, ℂ) => g x) (Ring.mul_inverse_cancel f hf)
  exact eq_inv_of_mul_eq_one_right hmul

/-- A contour quotient depends analytically on the parameter whenever its two
continuous-function-valued factors do and the denominator has no zero on the fixed
circle. The proof constructs a common nonvanishing neighborhood using openness of units. -/
theorem analyticAt_integral_div {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    {F G : ℂ → C(sphere c r, ℂ)} {u : ℂ}
    (hF : AnalyticAt ℂ F u) (hG : AnalyticAt ℂ G u)
    (hzero : ∀ z, F u z ≠ 0) :
    AnalyticAt ℂ (fun v => ∮ z in C(c, r),
      if hz : z ∈ sphere c r then G v ⟨z, hz⟩ / F v ⟨z, hz⟩ else 0) u := by
  have hunit : IsUnit (F u) := (F u).isUnit_iff_forall_ne_zero.mpr hzero
  have hinv : AnalyticAt ℂ (fun v => Ring.inverse (F v)) u := by
    have hi := analyticAt_inverse (𝕜 := ℂ) hunit.unit
    rw [hunit.unit_spec] at hi
    exact hi.comp hF
  have ha : AnalyticAt ℂ
      (fun v => continuousMapIntegral c r hr (G v * Ring.inverse (F v))) u :=
    ((continuousMapIntegral c r hr).analyticAt
      (G u * Ring.inverse (F u))).comp
        (f := fun v => G v * Ring.inverse (F v)) (hG.mul hinv)
  apply ha.congr
  have hevent : ∀ᶠ v in 𝓝 u, IsUnit (F v) :=
    hF.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
  filter_upwards [hevent] with v hv
  apply continuousMapIntegral_eq hr
  intro z hz
  simp only [dif_pos hz, ContinuousMap.mul_apply, inverse_apply (F v) hv, div_eq_mul_inv]

end circleIntegral
