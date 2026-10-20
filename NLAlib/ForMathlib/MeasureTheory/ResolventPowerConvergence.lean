import NLAlib.ForMathlib.MeasureTheory.ResolventPowerObservables
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Convergence of actual first resolvents determines all positive powers

Local uniform convergence of actual observable Bochner first-resolvent
means to a fixed self-adjoint model implies convergence of every positive
power mean. Genuine differentiated integrals and the complex uniform-limit
theorem supply the higher powers. The sample spaces and algebras may vary.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace MeasureTheory
variable {ι A₀ E : Type*} [CStarAlgebra A₀]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {Ω B : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [∀ i, CStarAlgebra (B i)]

/-- Actual observable resolvent power means converge locally uniformly
whenever their actual first-resolvent means do. -/
theorem tendstoLocallyUniformlyOn_resolventPowerMean_of_first
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsFiniteMeasure (μ i)]
    (X : (i : ι) → Ω i → selfAdjoint (B i))
    (hX : ∀ i, AEStronglyMeasurable (X i) (μ i))
    (L : (i : ι) → B i →L[ℂ] E) (a : selfAdjoint A₀) (L₀ : A₀ →L[ℂ] E)
    (p : Filter ι)
    (hfirst : TendstoLocallyUniformlyOn
      (fun i => resolventPowerMean (μ i) (X i) (L i) 1)
      (fun z : ℂ => L₀ (resolvent (a : A₀) z)) p {z : ℂ | 0<z.im})
    (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun i => resolventPowerMean (μ i) (X i) (L i) (k+1))
      (fun z : ℂ => L₀ (resolvent (a : A₀) z^(k+1))) p {z : ℂ | 0<z.im} := by
  induction k with
  | zero => simpa only [zero_add,pow_one] using hfirst
  | succ k ih =>
    let c : ℂ := -((k+1 : ℕ) : ℂ)
    have hc : c≠0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
    have hd := ih.deriv (Filter.Eventually.of_forall fun i =>
      differentiableOn_resolventPowerMean (X i) (hX i) (L i) (k+1))
      (isOpen_lt continuous_const Complex.continuous_im)
    have hs := (ContinuousLinearMap.lsmul ℂ ℂ (E := E) c⁻¹).uniformContinuous.comp_tendstoLocallyUniformlyOn hd
    refine (hs.congr fun i z hz => ?_).congr_right fun z hz => ?_
    · change c⁻¹•deriv (resolventPowerMean (μ i) (X i) (L i) (k+1)) z=
        resolventPowerMean (μ i) (X i) (L i) (k+1+1) z
      rw [(hasDerivAt_resolventPowerMean (X i) (hX i) (L i) (ne_of_gt hz) (k+1)).deriv]
      exact inv_smul_smul₀ hc _
    · change c⁻¹•deriv (fun w : ℂ => L₀ (resolvent (a : A₀) w^(k+1))) z=
        L₀ (resolvent (a : A₀) z^(k+1+1))
      rw [(hasDerivAt_linearMap_resolvent_pow L₀ a (ne_of_gt hz) (k+1)).deriv]
      exact inv_smul_smul₀ hc _

end MeasureTheory
