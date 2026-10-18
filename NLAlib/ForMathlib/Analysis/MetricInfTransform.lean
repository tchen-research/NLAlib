import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-! # The metric infimum transform

The transform `inf_y (dist x y - g y)` is one-Lipschitz and converts any
continuous additive pair below the metric cost into a single Lipschitz
potential. This is the metric step in compact transport duality.
-/

noncomputable section

open Set

namespace NLAlib

variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X]

/-- The metric cost transform of a continuous potential on a compact space. -/
def metricInfTransform (g : C(X, ℝ)) (x : X) : ℝ :=
  ⨅ y : X, dist x y - g y

private theorem bddBelow_metricInfTransform (g : C(X, ℝ)) (x : X) :
    BddBelow (range fun y : X => dist x y - g y) := by
  refine ⟨-‖g‖, ?_⟩
  rintro _ ⟨y, rfl⟩
  linarith [g.apply_le_norm y, dist_nonneg (x := x) (y := y)]

theorem metricInfTransform_le (g : C(X, ℝ)) (x y : X) :
    metricInfTransform g x ≤ dist x y - g y :=
  ciInf_le (bddBelow_metricInfTransform g x) y

theorem metricInfTransform_lipschitz [Nonempty X] (g : C(X, ℝ)) :
    LipschitzWith 1 (metricInfTransform g) := by
  apply LipschitzWith.of_le_add_mul 1
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro z
  have hx := metricInfTransform_le g x z
  have ht := dist_triangle x y z
  linarith

/-- A pair below the metric cost is dominated by a single one-Lipschitz
potential and its negative. -/
theorem exists_lipschitz_dominate_of_add_le_dist [Nonempty X]
    (f g : C(X, ℝ)) (hfg : ∀ x y, f x + g y ≤ dist x y) :
    ∃ u : C(X, ℝ), LipschitzWith 1 u ∧ (∀ x, f x ≤ u x) ∧ ∀ y, g y ≤ -u y := by
  let u : C(X, ℝ) := ⟨metricInfTransform g, (metricInfTransform_lipschitz g).continuous⟩
  refine ⟨u, metricInfTransform_lipschitz g, ?_, ?_⟩
  · intro x
    apply le_ciInf
    intro y
    have h := hfg x y
    linarith
  · intro y
    have h := metricInfTransform_le g y y
    simp only [dist_self, zero_sub] at h
    change g y ≤ -metricInfTransform g y
    linarith

end NLAlib
