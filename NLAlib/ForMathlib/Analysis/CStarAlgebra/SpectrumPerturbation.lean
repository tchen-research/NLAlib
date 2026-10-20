import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Spectral stability under perturbations of normal elements

The C*-algebra functional calculus and the Neumann unit criterion prove that
every point in a perturbed spectrum lies within the perturbation norm of the
original normal spectrum. For self-adjoint elements this gives both directions
of the real spectral inclusion. The statements include the trivial algebra.
-/

noncomputable section
set_option autoImplicit false

open scoped ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A]

/-- The actual resolvent of a normal element is its continuous inverse
function whenever the scalar lies outside the actual spectrum. -/
theorem IsStarNormal.resolvent_eq_cfc_of_notMem_spectrum {a : A}
    (ha : IsStarNormal a) {z : ℂ} (hz : z ∉ spectrum ℂ a) :
    resolvent a z = cfc (fun x : ℂ => (z - x)⁻¹) a := by
  have hf : ContinuousOn (fun x : ℂ => z - x) (spectrum ℂ a) :=
    (continuous_const.sub continuous_id).continuousOn
  have hshift : cfc (fun x : ℂ => z - x) a = algebraMap ℂ A z - a := by
    rw [cfc_sub (fun _ : ℂ => z) (fun x : ℂ => x) a
      continuous_const.continuousOn continuous_id.continuousOn,
      cfc_const z a ha, cfc_id' ℂ a ha]
  change Ring.inverse (algebraMap ℂ A z - a) = _
  rw [← hshift]
  apply (cfc_inv (fun x : ℂ => z - x) a _ hf ha).symm
  intro x hx hzx
  exact hz (sub_eq_zero.mp hzx ▸ hx)

/-- Every spectral point of an arbitrary perturbation lies within the norm
of that perturbation of a normal element's spectrum. This is the usual
normal spectral stability theorem in a complex C*-algebra. -/
theorem IsStarNormal.exists_mem_spectrum_dist_le_norm_sub {a b : A}
    (ha : IsStarNormal a) {z : ℂ} (hzb : z ∈ spectrum ℂ b) :
    ∃ w ∈ spectrum ℂ a, dist z w ≤ ‖a - b‖ := by
  by_cases hab : a = b
  · subst b
    exact ⟨z, hzb, by simp⟩
  have hδ : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  by_contra! hfar
  have hza : z ∉ spectrum ℂ a := by
    intro hz
    have h := hfar z hz
    simp only [dist_self] at h
    exact (not_lt_of_ge (norm_nonneg _)) h
  have hR : ‖resolvent a z‖ < ‖a - b‖⁻¹ := by
    rw [ha.resolvent_eq_cfc_of_notMem_spectrum hza]
    apply norm_cfc_lt (inv_pos.mpr hδ)
    intro x hx
    rw [norm_inv]
    have hdist : ‖a - b‖ < ‖z - x‖ := by simpa only [dist_eq_norm] using hfar x hx
    exact (inv_lt_inv₀ (hδ.trans hdist) hδ).mpr hdist
  have hsmall : ‖resolvent a z * (b - a)‖ < 1 := by
    calc
      _ ≤ ‖resolvent a z‖ * ‖a - b‖ := by
        simpa only [norm_sub_rev] using norm_mul_le (resolvent a z) (b - a)
      _ < ‖a - b‖⁻¹ * ‖a - b‖ := mul_lt_mul_of_pos_right hR hδ
      _ = 1 := inv_mul_cancel₀ hδ.ne'
  have hunitA : IsUnit (algebraMap ℂ A z - a) := spectrum.notMem_iff.mp hza
  have hunit := hunitA.mul (isUnit_one_sub_of_norm_lt_one hsmall)
  have hfactor : (algebraMap ℂ A z - a) * (1 - resolvent a z * (b - a)) =
      algebraMap ℂ A z - b := by
    rw [mul_sub, mul_one, ← mul_assoc,
      show (algebraMap ℂ A z - a) * resolvent a z = 1 from
        Ring.mul_inverse_cancel _ hunitA, one_mul]
    abel
  rw [hfactor] at hunit
  exact (spectrum.mem_iff.mp hzb) hunit

/-- A real spectral point of a perturbed self-adjoint element is within the
perturbation norm of the actual real spectrum of the original element. -/
theorem IsSelfAdjoint.exists_mem_spectrum_real_dist_le_norm_sub {a b : A}
    (ha : IsSelfAdjoint a) {x : ℝ} (hxb : x ∈ spectrum ℝ b) :
    ∃ y ∈ spectrum ℝ a, dist x y ≤ ‖a - b‖ := by
  have hx : (x : ℂ) ∈ spectrum ℂ b := spectrum.algebraMap_mem ℂ hxb
  obtain ⟨w, hw, hd⟩ := ha.isStarNormal.exists_mem_spectrum_dist_le_norm_sub hx
  have heq : w = (w.re : ℂ) := ha.mem_spectrum_eq_re hw
  refine ⟨w.re, ?_, ?_⟩
  · have hw' : (w.re : ℂ) ∈ spectrum ℂ a := by rw [← heq]; exact hw
    exact spectrum.of_algebraMap_mem ℂ hw'
  · rw [heq] at hd
    simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hd

end
