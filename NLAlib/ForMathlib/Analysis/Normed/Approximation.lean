import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/-!
# Nearest points in finite dimensional subspaces

A finite dimensional real subspace has a nearest point to every ambient vector. The proof
minimizes the continuous distance function on a compact ball in the subspace itself.
-/

noncomputable section

namespace NLAlib

/-- Every finite dimensional real subspace contains a nearest point to an ambient vector.
Source: the finite dimensional compactness proof of best approximation, Cheney (1966),
Chapter 2. The ambient normed space need not be finite dimensional or complete. -/
theorem exists_norm_sub_eq_infDist_of_finiteDimensional {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Submodule ℝ E)
    [FiniteDimensional ℝ S] (f : E) :
    ∃ p ∈ S, ‖f - p‖ = Metric.infDist f (S : Set E) := by
  let K : Set S := Metric.closedBall 0 (2 * ‖f‖)
  have hK : IsCompact K := isCompact_closedBall _ _
  have h0 : (0 : S) ∈ K := by simp [K, norm_nonneg]
  have hc : Continuous (fun p : S => ‖f - (p : E)‖) := by fun_prop
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn ⟨0, h0⟩ hc.continuousOn
  have hbest : ∀ q : S, ‖f - (p : E)‖ ≤ ‖f - (q : E)‖ := by
    intro q
    by_cases hq : q ∈ K
    · exact hmin hq
    · have hqnorm : 2 * ‖f‖ < ‖(q : E)‖ := by
        simpa [K, Metric.mem_closedBall, dist_zero_right] using hq
      have htri := norm_sub_norm_le (q : E) f
      rw [norm_sub_rev] at htri
      have hp0 : ‖f - (p : E)‖ ≤ ‖f - ((0 : S) : E)‖ := hmin h0
      simp only [Submodule.coe_zero, sub_zero] at hp0
      linarith
  refine ⟨p, p.property, le_antisymm ?_ ?_⟩
  · exact (Metric.le_infDist ⟨0, S.zero_mem⟩).mpr fun q hq => by
      simpa [dist_eq_norm] using hbest ⟨q, hq⟩
  · simpa [dist_eq_norm] using (Metric.infDist_le_dist_of_mem (x := f) p.property)

end NLAlib
