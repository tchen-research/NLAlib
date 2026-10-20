import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Squaring positive spectral sets across a gap

Compact real sets may contain zero and negative values. A positive gap
larger than the matching error makes their positive squared images
stable under Hausdorff perturbation, with the reference radius retained.
-/

noncomputable section
set_option autoImplicit false
namespace Metric

private theorem exists_mem_dist_le_of_hausdorffDist_le
    {S T : Set ℝ} (hS : IsCompact S) (hT : IsCompact T)
    (hSn : S.Nonempty) (hTn : T.Nonempty) {x δ : ℝ}
    (hx : x ∈ S) (hd : hausdorffDist S T ≤ δ) :
    ∃ y ∈ T, dist x y ≤ δ := by
  obtain ⟨y, hy, hdist⟩ := hT.exists_infDist_eq_dist hTn x
  refine ⟨y, hy, ?_⟩
  rw [← hdist]
  exact (infDist_le_hausdorffDist_of_mem hx
    (hausdorffEDist_ne_top_of_nonempty_of_bounded hSn hTn hS.isBounded hT.isBounded)).trans hd

private theorem abs_sq_sub_sq_le_of_reference_radius
    {x y δ R : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hδ : 0 ≤ δ)
    (hR : y ≤ R) (hd : |x - y| ≤ δ) :
    |x ^ 2 - y ^ 2| ≤ 2 * δ * R + δ ^ 2 := by
  have hxy : x + y ≤ 2 * R + δ := by
    have := (abs_le.mp hd).2
    linarith
  calc
    |x ^ 2 - y ^ 2| = |x - y| * (x + y) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg hx hy)]
      ring
    _ ≤ δ * (2 * R + δ) := mul_le_mul hd hxy (add_nonneg hx hy) hδ
    _ = 2 * δ * R + δ ^ 2 := by ring

/-- Squaring the positive parts of two actual compact real sets costs at
most `2 δ R + δ²` in Hausdorff distance. Every positive point is at least
`2δ`, so a point matched within `δ` is still positive; the theorem does
not identify zero padding with positive spectrum. The radius `R` bounds
only the positive part of the reference set `T`. -/
theorem hausdorffDist_sq_positive_le_of_gap
    {S T : Set ℝ} (hS : IsCompact S) (hT : IsCompact T)
    (hSn : S.Nonempty) (hTn : T.Nonempty) {δ R : ℝ} (hδ : 0 < δ)
    (hR : 0 ≤ R) (hgapS : ∀ x ∈ S, 0 < x → 2 * δ ≤ x)
    (hgapT : ∀ x ∈ T, 0 < x → 2 * δ ≤ x)
    (hrad : ∀ y ∈ T, 0 < y → y ≤ R)
    (hd : hausdorffDist S T ≤ δ) :
    hausdorffDist ((fun x : ℝ => x ^ 2) '' (S ∩ Set.Ioi 0))
      ((fun x : ℝ => x ^ 2) '' (T ∩ Set.Ioi 0)) ≤ 2 * δ * R + δ ^ 2 := by
  apply hausdorffDist_le_of_mem_dist (by positivity)
  · rintro _ ⟨x, ⟨hx, hx0⟩, rfl⟩
    obtain ⟨y, hy, hxy⟩ := exists_mem_dist_le_of_hausdorffDist_le hS hT hSn hTn hx hd
    have habs : |x - y| ≤ δ := by simpa only [Real.dist_eq] using hxy
    have hy0 : 0 < y := by
      have hxg := hgapS x hx hx0
      have hxy' := (abs_le.mp habs).2
      linarith
    refine ⟨y ^ 2, ⟨y, ⟨hy, hy0⟩, rfl⟩, ?_⟩
    simpa only [Real.dist_eq] using
      abs_sq_sub_sq_le_of_reference_radius hx0.le hy0.le hδ.le (hrad y hy hy0) habs
  · rintro _ ⟨y, ⟨hy, hy0⟩, rfl⟩
    obtain ⟨x, hx, hyx⟩ := exists_mem_dist_le_of_hausdorffDist_le hT hS hTn hSn hy
      (by simpa only [hausdorffDist_comm] using hd)
    have habs : |x - y| ≤ δ := by simpa only [Real.dist_eq, abs_sub_comm] using hyx
    have hx0 : 0 < x := by
      have hyg := hgapT y hy hy0
      have hxy' := (abs_le.mp habs).1
      linarith
    refine ⟨x ^ 2, ⟨x, ⟨hx, hx0⟩, rfl⟩, ?_⟩
    simpa only [Real.dist_eq, abs_sub_comm] using
      abs_sq_sub_sq_le_of_reference_radius hx0.le hy0.le hδ.le (hrad y hy hy0) habs

end Metric
