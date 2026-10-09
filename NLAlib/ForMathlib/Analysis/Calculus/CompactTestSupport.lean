import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact

/-!
# Positive compact test supports

Compact test functions supported in the positive half-line, together with their
derivatives, are supported in one fixed strictly positive bounded interval.
Atlas: wishart-lambda-min-tail.
-/

noncomputable section

open Set

namespace NLAlib

/-- A compactly supported real function in the positive half-line and its derivative
have support in one strictly positive compact interval. No nonzero assumption is
needed; the empty-support case is included.
Source: compactness and derivative support containment;
atlas wishart-lambda-min-tail (unshifted cutoff helper). -/
theorem exists_pos_bounds_tsupport_and_deriv (ψ : ℝ → ℝ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport ψ ⊆ Icc a b ∧ tsupport (deriv ψ) ⊆ Icc a b := by
  obtain ⟨a, ha, hlow⟩ := hψc.isCompact.exists_forall_le' continuous_id.continuousOn
    (fun x hx => hψs hx)
  obtain ⟨B, hB⟩ := hψc.isCompact.bddAbove
  let b := max a B + 1
  have hab : a < b := by dsimp [b]; linarith [le_max_left a B]
  have hs : tsupport ψ ⊆ Icc a b := by
    intro x hx
    refine ⟨hlow x hx, ?_⟩
    have hxb : x ≤ B := hB hx
    dsimp [b]
    linarith [le_max_right a B]
  exact ⟨a, b, ha, hab, hs, tsupport_deriv_subset.trans hs⟩

end NLAlib
