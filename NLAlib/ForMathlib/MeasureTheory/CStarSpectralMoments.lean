import NLAlib.ForMathlib.MeasureTheory.CStarSpectralMeasure
import NLAlib.ForMathlib.Analysis.CStarAlgebra.ResolventModulus

/-!
# Native Gram moments as actual scalar spectral Lp norms

The Riesz--Markov spectrum measure of the actual positive functional turns
even scalar Lp norms into the native noncommutative Gram moments. Applied
to the resolvent modulus this supplies the moment bridge in Theorem 4.2 of
arXiv:2406.11453v2, without an assumed abstract moment model.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped ComplexOrder ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem realMomentCFC : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)).toContinuousFunctionalCalculus

attribute [local instance] realMomentCFC

/-- A continuous real scalar function's actual spectral L`4q` norm equals
the rooted native Gram moment of its genuine continuous functional calculus. -/
theorem lpNorm_positiveSpectrumMeasure_eq_gramMoment (φ : A →ₚ[ℂ] ℂ)
    {a : A} (ha : IsSelfAdjoint a) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ a)) (q : ℕ) (hq : 0 < q) :
    lpNorm (fun x : spectrum ℝ a => f x) (4 * q : ENNReal)
        (positiveSpectrumMeasure φ ha) =
      ((φ ((star (cfc f a) * cfc f a) ^ (2 * q))).re) ^ ((4 * q : ℝ)⁻¹) := by
  have hp : 0 < 4 * q := by omega
  have hself : IsSelfAdjoint (cfc f a) := IsSelfAdjoint.cfc
  have hc : cfc (fun x : ℝ => |f x| ^ (4 * q)) a =
      (star (cfc f a) * cfc f a) ^ (2 * q) := by
    calc
      _ = cfc (fun x : ℝ => f x ^ (4 * q)) a := by
        apply cfc_congr
        intro x hx
        exact (show Even (4 * q) from ⟨2 * q, by omega⟩).pow_abs _
      _ = cfc f a ^ (4 * q) := cfc_pow f (4 * q) a hf ha
      _ = (star (cfc f a) * cfc f a) ^ (2 * q) := by
        rw [hself.star_eq, ← pow_two, ← pow_mul]
        congr 1
        omega
  simpa only [Nat.cast_mul, Nat.cast_ofNat, hc] using
    lpNorm_positiveSpectrumMeasure_eq φ ha f hf (4 * q) hp

/-- The inverse-distance function on the actual spectrum has precisely
the rooted native Gram moment of the original nonreal resolvent. -/
theorem lpNorm_positiveSpectrumMeasure_resolvent_modulus (φ : A →ₚ[ℂ] ℂ)
    {a : A} (ha : IsSelfAdjoint a) {z : ℂ} (hz : z.im ≠ 0)
    (q : ℕ) (hq : 0 < q) :
    lpNorm (fun x : spectrum ℝ a => ‖(z - (x : ℂ))⁻¹‖) (4 * q : ENNReal)
        (positiveSpectrumMeasure φ ha) =
      ((φ ((star (resolvent a z) * resolvent a z) ^ (2 * q))).re) ^
        ((4 * q : ℝ)⁻¹) := by
  have hnonzero (x : ℝ) : z - (x : ℂ) ≠ 0 := by
    intro h
    apply hz
    have heq : z = (x : ℂ) := sub_eq_zero.mp h
    rw [heq]
    rfl
  have hf : ContinuousOn (fun x : ℝ => ‖(z - (x : ℂ))⁻¹‖) (spectrum ℝ a) :=
    ((continuous_const.sub Complex.continuous_ofReal).inv₀ hnonzero).norm.continuousOn
  rw [lpNorm_positiveSpectrumMeasure_eq_gramMoment φ ha _ hf q hq,
    ← ha.abs_resolvent_eq_cfc hz]
  congr 3
  have hself : IsSelfAdjoint (CFC.abs (resolvent a z)) := (CFC.abs_nonneg _).isSelfAdjoint
  rw [hself.star_eq, ← pow_two, CFC.abs_sq]

end
