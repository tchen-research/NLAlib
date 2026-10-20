import NLAlib.ForMathlib.MeasureTheory.ResolventPowerIntegrals

/-!
# Actual continuous linear observables of resolvent power means

An actual bounded linear observable of the Bochner resolvent mean has the
same exact power derivative. This supports native partial traces and vacuum
compressions, with their own actual laws and operators.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace MeasureTheory
variable {Ω A E : Type*} [MeasurableSpace Ω] [CStarAlgebra A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Apply an actual continuous linear observable to the genuine Bochner mean of a resolvent power. -/
def resolventPowerMean (μ : Measure Ω) (X : Ω → selfAdjoint A)
    (L : A →L[ℂ] E) (n : ℕ) (z : ℂ) : E :=
  L (∫ ω, resolvent (X ω : A) z^n ∂μ)

variable {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The actual observable mean has derivative equal to the negative exponent times its next power mean. -/
theorem hasDerivAt_resolventPowerMean
    (X : Ω → selfAdjoint A) (hX : AEStronglyMeasurable X μ)
    (L : A →L[ℂ] E) {z : ℂ} (hz : z.im≠0) (n : ℕ) :
    HasDerivAt (resolventPowerMean μ X L n)
      (-(n : ℂ)•resolventPowerMean μ X L (n+1) z) z := by
  unfold resolventPowerMean
  have h := L.hasFDerivAt.comp_hasDerivAt z
    (hasDerivAt_integral_resolvent_selfAdjoint_pow X hX hz n)
  simpa only [Function.comp_def,map_smul] using h

/-- Every actual observable resolvent power mean is holomorphic on the upper half-plane. -/
theorem differentiableOn_resolventPowerMean
    (X : Ω → selfAdjoint A) (hX : AEStronglyMeasurable X μ)
    (L : A →L[ℂ] E) (n : ℕ) :
    DifferentiableOn ℂ (resolventPowerMean μ X L n) {z : ℂ | 0<z.im} := by
  intro z hz
  exact (hasDerivAt_resolventPowerMean X hX L (ne_of_gt hz) n).differentiableAt.differentiableWithinAt

/-- Every continuous linear observable of a fixed self-adjoint resolvent has its genuine power derivative. -/
theorem hasDerivAt_linearMap_resolvent_pow
    (L : A →L[ℂ] E) (a : selfAdjoint A) {z : ℂ} (hz : z.im≠0) (n : ℕ) :
    HasDerivAt (fun w : ℂ => L (resolvent (a : A) w^n))
      (-(n : ℂ)•L (resolvent (a : A) z^(n+1))) z := by
  have h := L.hasFDerivAt.comp_hasDerivAt z (spectrum.hasDerivAt_resolvent_pow (a : A)
    (a.property.isUnit_algebraMap_sub_of_im_ne_zero hz) n)
  simpa only [Function.comp_def,map_smul] using h

end MeasureTheory
