import NLAlib.ForMathlib.MeasureTheory.CStarSpectralMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Rooted positive moments dominate the first moment

The actual spectrum probability measure of a normalized positive
functional reduces the estimate to scalar monotonicity of Lp exponents.
No trace assumption or operator convexity premise is needed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ComplexOrder ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem realMomentJensenCFC : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)).toContinuousFunctionalCalculus

attribute [local instance] realMomentJensenCFC

/-- A genuine normalized positive functional's rooted positive integer
moment dominates its first moment, by scalar Lp exponent comparison on
the actual spectrum measure. -/
theorem PositiveLinearMap.re_le_re_pow_rpow (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1)
    {a : A} (ha : 0≤a) (m : ℕ) (hm : 0<m) :
    (φ a).re≤((φ (a^m)).re)^((m : ℝ)⁻¹) := by
  have hself : IsSelfAdjoint a := ha.isSelfAdjoint
  let μ := positiveSpectrumMeasure φ hself
  let : IsProbabilityMeasure μ := isProbabilityMeasure_positiveSpectrumMeasure φ hφ hself
  let f : spectrum ℝ a → ℝ := fun x => (x : ℝ)
  have hf : Continuous f := continuous_subtype_val
  have hmem : MemLp f (m : ENNReal) μ :=
    hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp : (1 : ENNReal)≤m := by exact_mod_cast (Nat.succ_le_of_lt hm)
  have hLp : lpNorm f 1 μ≤lpNorm f (m : ENNReal) μ := by
    calc
      _ = (eLpNorm f 1 μ).toReal := (toReal_eLpNorm hmem.aestronglyMeasurable).symm
      _ ≤ (eLpNorm f (m : ENNReal) μ).toReal := ENNReal.toReal_mono hmem.eLpNorm_ne_top
        (eLpNorm_le_eLpNorm_of_exponent_le hp hmem.aestronglyMeasurable)
      _ = _ := toReal_eLpNorm hmem.aestronglyMeasurable
  have hcalc (n : ℕ) : cfc (fun x : ℝ => |x|^n) a=a^n := by
    calc
      _ = cfc (fun x : ℝ => x^n) a := by
        apply cfc_congr
        intro x hx
        change |x|^n=x^n
        rw [abs_of_nonneg (spectrum_nonneg_of_nonneg ha hx)]
      _ = _ := cfc_pow_id a n hself
  have hfirst : lpNorm f 1 μ=(φ a).re := by
    have habs : cfc (fun x : ℝ => |x|) a=a := by simpa only [pow_one] using hcalc 1
    simpa only [pow_one,habs,Nat.cast_one,inv_one,Real.rpow_one] using
      lpNorm_positiveSpectrumMeasure_eq φ hself (fun x : ℝ => x)
        continuous_id.continuousOn 1 (by decide)
  have hlast : lpNorm f (m : ENNReal) μ=((φ (a^m)).re)^((m : ℝ)⁻¹) := by
    simpa only [hcalc] using lpNorm_positiveSpectrumMeasure_eq φ hself (fun x : ℝ => x)
      continuous_id.continuousOn m hm
  rwa [hfirst,hlast] at hLp

end
