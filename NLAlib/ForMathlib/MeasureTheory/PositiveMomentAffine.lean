import NLAlib.ForMathlib.MeasureTheory.CStarSpectralMeasure
import NLAlib.ForMathlib.MeasureTheory.LpUniformApproximation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Genuine positive affine moment bounds

The actual spectrum measure of a normalized positive functional reduces an
affine positive-power estimate to Mathlib's scalar Lp triangle inequality.
No traciality or noncommutative Minkowski theorem is assumed in this scalar
functional-calculus step.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ComplexOrder ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem realAffineCFC : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)).toContinuousFunctionalCalculus

attribute [local instance] realAffineCFC

/-- Actual rooted moments of a positive affine function satisfy the scalar
Minkowski bound, derived on the element's genuine spectrum probability
measure. The functional need not be tracial. -/
theorem PositiveLinearMap.re_pow_affine_rpow_le (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    {a : A} (ha : 0 ≤ a) {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (m : ℕ) (hm : 0 < m) :
    ((φ ((s • a + algebraMap ℝ A c) ^ m)).re) ^ ((m : ℝ)⁻¹) ≤
      s * ((φ (a ^ m)).re) ^ ((m : ℝ)⁻¹) + c := by
  have hself : IsSelfAdjoint a := ha.isSelfAdjoint
  let hprob : IsProbabilityMeasure (positiveSpectrumMeasure φ hself) :=
    isProbabilityMeasure_positiveSpectrumMeasure φ hφ hself
  have hp : (1 : ENNReal) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hmem : MemLp (fun x : spectrum ℝ a => s * (x : ℝ)) (m : ENNReal)
      (positiveSpectrumMeasure φ hself) :=
    ((continuous_const.mul continuous_subtype_val).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hLp := lpNorm_le_add_of_uniform_approximation hmem hp (by simp) hc
    (f := fun x : spectrum ℝ a => s * (x : ℝ) + c)
    (fun x => by simp only [add_sub_cancel_left,abs_of_nonneg hc,le_refl])
  have hcfcid : cfc (fun x : ℝ => |x| ^ m) a = a ^ m := by
    calc
      _ = cfc (fun x : ℝ => x ^ m) a := by
        apply cfc_congr
        intro x hx
        change |x|^m=x^m
        rw [abs_of_nonneg (spectrum_nonneg_of_nonneg ha hx)]
      _ = _ := cfc_pow_id a m hself
  have hcfcaff : cfc (fun x : ℝ => |s*x+c| ^ m) a =
      (s • a + algebraMap ℝ A c) ^ m := by
    calc
      _ = cfc (fun x : ℝ => (s*x+c) ^ m) a := by
        apply cfc_congr
        intro x hx
        change |s*x+c|^m=(s*x+c)^m
        rw [abs_of_nonneg (add_nonneg (mul_nonneg hs
          (spectrum_nonneg_of_nonneg ha hx)) hc)]
      _ = cfc (fun x : ℝ => s*x+c) a ^ m :=
        cfc_pow _ m a ((continuous_const.mul continuous_id).add continuous_const).continuousOn hself
      _ = _ := by
        rw [cfc_add_const c (fun x : ℝ => s*x) a
          (continuous_const.mul continuous_id).continuousOn hself,
          cfc_const_mul_id s a hself]
  have hid : lpNorm (fun x : spectrum ℝ a => (x : ℝ)) (m : ENNReal)
      (positiveSpectrumMeasure φ hself) = ((φ (a ^ m)).re) ^ ((m : ℝ)⁻¹) := by
    simpa only [hcfcid] using lpNorm_positiveSpectrumMeasure_eq φ hself
      (fun x : ℝ => x) continuous_id.continuousOn m hm
  have haff : lpNorm (fun x : spectrum ℝ a => s * (x : ℝ) + c) (m : ENNReal)
      (positiveSpectrumMeasure φ hself) =
        ((φ ((s • a + algebraMap ℝ A c) ^ m)).re) ^ ((m : ℝ)⁻¹) := by
    simpa only [hcfcaff] using lpNorm_positiveSpectrumMeasure_eq φ hself
      (fun x : ℝ => s*x+c) ((continuous_const.mul continuous_id).add continuous_const).continuousOn m hm
  have hscale : lpNorm (fun x : spectrum ℝ a => s * (x : ℝ)) (m : ENNReal)
      (positiveSpectrumMeasure φ hself) =
        s * ((φ (a ^ m)).re) ^ ((m : ℝ)⁻¹) := by
    calc
      _ = ‖s‖ * lpNorm (fun x : spectrum ℝ a => (x : ℝ)) (m : ENNReal)
          (positiveSpectrumMeasure φ hself) :=
        lpNorm_const_smul s _ _
      _ = _ := by rw [Real.norm_eq_abs,abs_of_nonneg hs,hid]
  rwa [haff,hscale] at hLp

end
