import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Spectral measures of actual positive functionals

Real continuous functional calculus and Riesz--Markov construct a finite
measure on the actual compact spectrum of a self-adjoint element. Its mass
is the actual functional's value at one. No trace, faithfulness, representing
measure or moment formula is assumed.

This generalizes the construction in
`NLAlib.Probability.Free.WordFieldSpectralMeasure` for use with matrix-valued
word polynomials and their actual amplified vacuum functional.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped ComplexOrder CompactlySupported ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem realCFC : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)).toContinuousFunctionalCalculus

attribute [local instance] realCFC

private def compactlySupportedToContinuousLinearMap (X : Type*) [TopologicalSpace X] :
    C_c(X, ℝ) →ₗ[ℝ] C(X, ℝ) where
  toFun f := f.toContinuousMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual real positive spectral functional obtained by composing
continuous functional calculus with a complex positive functional. -/
def positiveSpectralFunctional (φ : A →ₚ[ℂ] ℂ) {a : A} (ha : IsSelfAdjoint a) :
    C_c(spectrum ℝ a, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    ((Complex.reCLM.toLinearMap.comp (φ.toLinearMap.restrictScalars ℝ)).comp
      ((cfcHom (R := ℝ) ha).toLinearMap.comp
        (compactlySupportedToContinuousLinearMap (spectrum ℝ a)))) fun f hf => by
    have hC : 0 ≤ cfcHom (R := ℝ) ha f.toContinuousMap :=
      (cfcHom_nonneg_iff _).mpr hf
    exact (Complex.nonneg_iff.mp (φ.map_nonneg hC)).1

/-- The defining spectral functional is the genuine functional-calculus
value of the actual positive functional. -/
@[simp]
theorem positiveSpectralFunctional_apply (φ : A →ₚ[ℂ] ℂ) {a : A}
    (ha : IsSelfAdjoint a) (f : C_c(spectrum ℝ a, ℝ)) :
    positiveSpectralFunctional φ ha f = (φ (cfcHom (R := ℝ) ha f.toContinuousMap)).re := rfl

/-- The actual Riesz--Markov measure on the native compact real spectrum. -/
def positiveSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) {a : A} (ha : IsSelfAdjoint a) :
    Measure (spectrum ℝ a) :=
  RealRMK.rieszMeasure (positiveSpectralFunctional φ ha)

instance isFiniteMeasure_positiveSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) {a : A}
    (ha : IsSelfAdjoint a) : IsFiniteMeasure (positiveSpectrumMeasure φ ha) :=
  inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure (positiveSpectralFunctional φ ha)))

/-- Integrating a continuous real function gives exactly the actual
positive functional applied to its native continuous functional calculus. -/
theorem integral_positiveSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) {a : A}
    (ha : IsSelfAdjoint a) (f : C(spectrum ℝ a, ℝ)) :
    ∫ x, f x ∂positiveSpectrumMeasure φ ha = (φ (cfcHom (R := ℝ) ha f)).re := by
  let fc : C_c(spectrum ℝ a, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (positiveSpectralFunctional φ ha) fc

/-- The actual spectrum measure's total mass is the real value of the
original functional at the algebra identity. -/
theorem measureReal_univ_positiveSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) {a : A}
    (ha : IsSelfAdjoint a) : (positiveSpectrumMeasure φ ha).real Set.univ = (φ 1).re := by
  have h := integral_positiveSpectrumMeasure φ ha (1 : C(spectrum ℝ a, ℝ))
  simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one, map_one] using h

/-- A normalized actual positive functional yields an actual probability
measure on every self-adjoint element's native real spectrum. -/
theorem isProbabilityMeasure_positiveSpectrumMeasure (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    {a : A} (ha : IsSelfAdjoint a) : IsProbabilityMeasure (positiveSpectrumMeasure φ ha) := by
  rw [isProbabilityMeasure_iff_real, measureReal_univ_positiveSpectrumMeasure, hφ, Complex.one_re]

/-- The integral identity applies directly to any real function continuous
on the actual spectrum, with no global continuity or integrability premise. -/
theorem integral_comp_subtype_positiveSpectrumMeasure (φ : A →ₚ[ℂ] ℂ)
    {a : A} (ha : IsSelfAdjoint a) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ a)) :
    ∫ x : spectrum ℝ a, f x ∂positiveSpectrumMeasure φ ha = (φ (cfc f a)).re := by
  rw [cfc_apply f a ha hf]
  exact integral_positiveSpectrumMeasure φ ha ⟨fun x => f x, hf.domRestrict⟩

/-- Native scalar Lp norms on the constructed spectrum measure are exactly
the rooted positive-functional moments of the same continuous function. -/
theorem lpNorm_positiveSpectrumMeasure_eq (φ : A →ₚ[ℂ] ℂ)
    {a : A} (ha : IsSelfAdjoint a) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ a)) (p : ℕ) (hp : 0 < p) :
    lpNorm (fun x : spectrum ℝ a => f x) (p : ENNReal) (positiveSpectrumMeasure φ ha) =
      ((φ (cfc (fun x : ℝ => |f x| ^ p) a)).re) ^ ((p : ℝ)⁻¹) := by
  have hm : AEStronglyMeasurable (fun x : spectrum ℝ a => f x) (positiveSpectrumMeasure φ ha) :=
    hf.domRestrict.aestronglyMeasurable
  rw [lpNorm_eq_integral_norm_rpow_toReal (f := fun x : spectrum ℝ a => f x)
    (p := (p : ENNReal)) (by exact_mod_cast hp.ne') (by simp) hm]
  rw [← integral_comp_subtype_positiveSpectrumMeasure φ ha
    (fun x : ℝ => |f x| ^ p) (hf.abs.pow p)]
  simp only [ENNReal.toReal_natCast, Real.norm_eq_abs, Real.rpow_natCast]

end
