import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A continuous function bound from subsequential right variations

The scalar extreme-value argument turns upper bounds on subsequential right
difference quotients into an endpoint increment bound. It needs no derivatives
or integrals and is used by the compact-eigenframe proof of Lidskii.
-/

noncomputable section
open Filter Topology

namespace NLAlib

/-- A continuous real function on `[0,1]` grows by at most `L` if at every point
before the right endpoint its positive-step quotients admit a subsequence
converging to a value at most `L`. Scalar minimum argument, Lidskii operator route.
-/
theorem sub_le_of_continuous_of_subseq_difference_quotient_le
    (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc 0 1)) (L : ℝ)
    (hv : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∃ c ≤ L, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun ν => (F (t + (1 - t) / ((φ ν : ℝ) + 2)) - F t) /
        ((1 - t) / ((φ ν : ℝ) + 2))) atTop (𝓝 c)) :
    F 1 - F 0 ≤ L := by
  by_contra hle
  let ε := (F 1 - F 0 - L) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : L + ε < F 1 - F 0 := by dsimp [ε]; linarith
  let G : ℝ → ℝ := fun t => F t - (L + ε) * t
  have hG : ContinuousOn G (Set.Icc 0 1) := hF.sub (continuous_const.mul continuous_id).continuousOn
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) hG
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t < 1 := by
    have hmin0 := hmin (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    change G t ≤ G 0 at hmin0
    have hne : t ≠ 1 := by
      intro heq
      simp only [heq, G, mul_zero, sub_zero, mul_one] at hmin0
      linarith
    exact lt_of_le_of_ne ht.2 hne
  obtain ⟨c, hc, φ, _, hlim⟩ := hv t ⟨ht.1, ht1⟩
  have hquot (ν : ℕ) : L + ε ≤
      (F (t + (1 - t) / ((φ ν : ℝ) + 2)) - F t) / ((1 - t) / ((φ ν : ℝ) + 2)) := by
    have hden : 0 < (φ ν : ℝ) + 2 := by positivity
    have hstep : 0 < (1 - t) / ((φ ν : ℝ) + 2) := div_pos (by linarith) hden
    have hstepBound : (1 - t) / ((φ ν : ℝ) + 2) ≤ 1 - t := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [show (0 : ℝ) ≤ (φ ν : ℝ) from Nat.cast_nonneg _]
    have hminStep := hmin (show t + (1 - t) / ((φ ν : ℝ) + 2) ∈ Set.Icc 0 1 by
      constructor <;> linarith)
    change G t ≤ G (t + (1 - t) / ((φ ν : ℝ) + 2)) at hminStep
    apply (le_div_iff₀ hstep).mpr
    dsimp [G] at hminStep
    nlinarith
  have hLc : L + ε ≤ c := ge_of_tendsto hlim (Filter.Eventually.of_forall hquot)
  linarith

end NLAlib
