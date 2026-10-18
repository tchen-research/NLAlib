import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# A first-order limit for the C⋆-algebra absolute value at the identity

The exact factorization `(abs a - 1) * (abs a + 1) = star a * a - 1`
reduces this limit to continuity of absolute value and inversion near `2`.
No differentiability theorem for an unspecified matrix square root is assumed.
-/

noncomputable section

open Filter
open scoped Topology

namespace CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If a rescaled perturbation of the identity converges to a self-adjoint
element, taking the actual C⋆-algebra absolute value preserves that limit. -/
theorem tendsto_smul_abs_sub_one_of_tendsto_smul_sub_one
    {ι : Type*} {l : Filter ι} {a : ι → A} {t : ι → ℝ} {S : A}
    (ha : Tendsto a l (𝓝 1))
    (hs : Tendsto (fun i => t i • (a i - 1)) l (𝓝 S))
    (hS : IsSelfAdjoint S) :
    Tendsto (fun i => t i • (abs (a i) - 1)) l (𝓝 S) := by
  have hstar : Tendsto (fun i => t i • (star (a i) - 1)) l (𝓝 S) := by
    have h := hs.star
    simpa only [star_smul, star_trivial, star_sub, star_one, hS.star_eq] using h
  have hgram : Tendsto (fun i => t i • (star (a i) * a i - 1)) l (𝓝 (S + S)) := by
    have h := (hstar.mul ha).add hs
    simp only [mul_one] at h
    apply h.congr' (Eventually.of_forall fun i => ?_)
    rw [smul_mul_assoc, ← smul_add]
    congr 1
    noncomm_ring
  have hq : Tendsto (fun i => abs (a i) + 1) l (𝓝 ((1 : A) + 1)) := by
    simpa only [Function.comp_def, abs_one] using
      ((CFC.continuous_abs.continuousAt.tendsto.comp ha).add_const 1)
  have hunit : IsUnit ((1 : A) + 1) := by
    have he : (algebraMap ℝ A) 2 = (1 : A) + 1 := by
      calc
        _ = (algebraMap ℝ A) ((1 : ℝ) + 1) := by norm_num
        _ = _ := by rw [map_add, map_one]
    rw [← he]
    exact (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : ℝ) ≠ 0)).map (algebraMap ℝ A)
  have hinvc : ContinuousAt (Ring.inverse : A → A) ((1 : A) + 1) := by
    obtain ⟨u, hu⟩ := hunit
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hinv := hinvc.tendsto.comp hq
  have hqunit : ∀ᶠ i in l, IsUnit (abs (a i) + 1) :=
    hq.eventually (Units.isOpen.mem_nhds hunit)
  have hprod := hgram.mul hinv
  have hcenter : (S + S) * Ring.inverse ((1 : A) + 1) = S := by
    calc
      _ = (S * ((1 : A) + 1)) * Ring.inverse ((1 : A) + 1) := by rw [mul_add, mul_one]
      _ = S := by rw [mul_assoc, Ring.mul_inverse_cancel _ hunit, mul_one]
  rw [hcenter] at hprod
  apply hprod.congr'
  filter_upwards [hqunit] with i hi
  dsimp only [Function.comp_apply]
  have hfactor : (abs (a i) - 1) * (abs (a i) + 1) = star (a i) * a i - 1 := by
    calc
      _ = abs (a i) * abs (a i) - 1 := by noncomm_ring
      _ = _ := by rw [abs_mul_abs]
  rw [← hfactor, smul_mul_assoc, mul_assoc, Ring.mul_inverse_cancel _ hi, mul_one]

end CFC
