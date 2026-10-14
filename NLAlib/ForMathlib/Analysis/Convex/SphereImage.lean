import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear images of spheres with nontrivial kernel

When a real linear map has a nonzero kernel vector, every point in the image
of the unit ball is already in the image of the unit sphere. The image is
therefore convex. This geometric fact supplies the Toeplitz–Hausdorff proof.
-/

noncomputable section
open scoped Topology
namespace LinearMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [AddCommGroup F] [Module ℝ F]

/-- A real linear map with nontrivial kernel sends the unit sphere onto the
same set as the closed unit ball. A continuous norm along a kernel ray
supplies a unit preimage without an inner-product assumption. -/
theorem image_sphere_eq_image_closedBall_of_ker_ne_bot (L : E →ₗ[ℝ] F)
    (hker : LinearMap.ker L ≠ ⊥) :
    L '' Metric.sphere 0 1 = L '' Metric.closedBall 0 1 := by
  apply Set.Subset.antisymm (Set.image_mono Metric.sphere_subset_closedBall)
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨v, hv, hv0⟩ := (LinearMap.ker L).ne_bot_iff.mp hker
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  have hLu : L u = 0 := by simp only [u, map_smul, LinearMap.mem_ker.mp hv, smul_zero]
  have hxnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  let f : ℝ → ℝ := fun t => ‖x + t • u‖
  have hc : Continuous f := by unfold f; fun_prop
  have hlow : f 0 ≤ 1 := by simpa [f] using hxnorm
  have hhigh : 1 ≤ f 2 := by
    have h := norm_add_le (x + (2 : ℝ) • u) (-x)
    have heq : x + (2 : ℝ) • u + -x = (2 : ℝ) • u := by abel
    rw [heq, norm_smul, Real.norm_of_nonneg (by norm_num), hu, norm_neg] at h
    dsimp only [f]
    linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2)
    hc.continuousOn ⟨hlow, hhigh⟩
  refine ⟨x + t • u, ?_, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using ht
  · rw [map_add, map_smul, hLu, smul_zero, add_zero]

/-- A real linear map with nontrivial kernel has a convex unit-sphere image,
because that image equals the linear image of the closed unit ball. -/
theorem convex_image_sphere_of_ker_ne_bot (L : E →ₗ[ℝ] F)
    (hker : LinearMap.ker L ≠ ⊥) : Convex ℝ (L '' Metric.sphere 0 1) := by
  rw [L.image_sphere_eq_image_closedBall_of_ker_ne_bot hker]
  exact (convex_closedBall (0 : E) 1).linear_image L

end LinearMap
