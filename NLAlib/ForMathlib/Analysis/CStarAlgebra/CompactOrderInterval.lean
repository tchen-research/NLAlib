import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Compact order intervals in proper C-star algebras

The actual C-star norm controls each positive order interval by a metric
ball. This includes finite-dimensional Hermitian matrix intervals.
-/

noncomputable section
set_option autoImplicit false
open Set Metric
namespace CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [OrderClosedTopology A] [ProperSpace A]

/-- Every order interval in a proper C-star algebra is compact: its
translation by its left endpoint lies in a positive norm ball. -/
theorem isCompact_Icc (a b : A) : IsCompact (Icc a b) := by
  apply (isCompact_closedBall a ‖b - a‖).of_isClosed_subset isClosed_Icc
  intro x hx
  have hp : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have hle : x - a ≤ b - a := sub_le_sub_right hx.2 a
  simpa only [mem_closedBall, dist_eq_norm] using norm_le_norm_of_nonneg_of_le hp hle

end CStarAlgebra
