import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-! # Extremal points of compact real sets and Hausdorff distance -/

noncomputable section
set_option autoImplicit false
namespace Metric

/-- The suprema of two nonempty compact real sets differ by at most
their actual Hausdorff distance. -/
theorem abs_csSup_sub_csSup_le_hausdorffDist
    {S T : Set ℝ} (hS : IsCompact S) (hT : IsCompact T)
    (hSn : S.Nonempty) (hTn : T.Nonempty) :
    |sSup S-sSup T| ≤ hausdorffDist S T := by
  have hf := hausdorffEDist_ne_top_of_nonempty_of_bounded hSn hTn hS.isBounded hT.isBounded
  have hst : sSup S-sSup T ≤ hausdorffDist S T := by
    obtain ⟨y,hy,he⟩ := hT.exists_infDist_eq_dist hTn (sSup S)
    have hd := infDist_le_hausdorffDist_of_mem (hS.sSup_mem hSn) hf
    rw [he,Real.dist_eq] at hd
    have hY := le_csSup hT.bddAbove hy
    linarith only [le_abs_self (sSup S-y),hd,hY]
  have hts : sSup T-sSup S ≤ hausdorffDist S T := by
    obtain ⟨x,hx,he⟩ := hS.exists_infDist_eq_dist hSn (sSup T)
    have hf' := hausdorffEDist_ne_top_of_nonempty_of_bounded hTn hSn hT.isBounded hS.isBounded
    have hd := infDist_le_hausdorffDist_of_mem (hT.sSup_mem hTn) hf'
    rw [he,Real.dist_eq,hausdorffDist_comm] at hd
    have hX := le_csSup hS.bddAbove hx
    linarith only [le_abs_self (sSup T-x),hd,hX]
  exact abs_le.mpr ⟨by linarith only [hts],hst⟩

/-- The infima of two nonempty compact real sets differ by at most
their actual Hausdorff distance. -/
theorem abs_csInf_sub_csInf_le_hausdorffDist
    {S T : Set ℝ} (hS : IsCompact S) (hT : IsCompact T)
    (hSn : S.Nonempty) (hTn : T.Nonempty) :
    |sInf S-sInf T| ≤ hausdorffDist S T := by
  have hf := hausdorffEDist_ne_top_of_nonempty_of_bounded hSn hTn hS.isBounded hT.isBounded
  have hst : sInf S-sInf T ≤ hausdorffDist S T := by
    obtain ⟨x,hx,he⟩ := hS.exists_infDist_eq_dist hSn (sInf T)
    have hf' := hausdorffEDist_ne_top_of_nonempty_of_bounded hTn hSn hT.isBounded hS.isBounded
    have hd := infDist_le_hausdorffDist_of_mem (hT.sInf_mem hTn) hf'
    rw [he,Real.dist_eq,hausdorffDist_comm] at hd
    have hX := csInf_le hS.bddBelow hx
    linarith only [neg_le_abs (sInf T-x),hd,hX]
  have hts : sInf T-sInf S ≤ hausdorffDist S T := by
    obtain ⟨y,hy,he⟩ := hT.exists_infDist_eq_dist hTn (sInf S)
    have hd := infDist_le_hausdorffDist_of_mem (hS.sInf_mem hSn) hf
    rw [he,Real.dist_eq] at hd
    have hY := csInf_le hT.bddBelow hy
    linarith only [neg_le_abs (sInf S-y),hd,hY]
  exact abs_le.mpr ⟨by linarith only [hts],hst⟩

end Metric
