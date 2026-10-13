import NLAlib.Matrix.Inequalities.MajorizationHinges
import NLAlib.Matrix.Inequalities.MajorizationWeakSupport
import NLAlib.Matrix.Inequalities.MajorizationHLP

/-!
# Full convex-function criteria for majorization

The downward closure of the compact permutation polytope gives the full weak
majorization criterion without a piecewise-linear interpolation argument.
Source: Marshall–Olkin–Arnold (2011), Propositions 4.B.1–4.B.2.
Atlas: `majorization-def`.
-/

noncomputable section
open scoped Pointwise

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A weakly majorized vector is coordinatewise below an ordinary-majorized
vector. This is proved by separation of the closed downward permutation polytope.
Marshall–Olkin–Arnold (2011), Proposition 4.B.2. -/
theorem WeaklyMajorized.exists_le_majorized {x y : ι → ℝ} (hxy : WeaklyMajorized x y) :
    ∃ z : ι → ℝ, x ≤ z ∧ Majorized z y := by
  let K := convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ)
  let C := K + Set.Iic (0 : ι → ℝ)
  have hK : IsCompact K := (Set.finite_range (fun σ : Equiv.Perm ι => y ∘ σ)).isCompact_convexHull ℝ
  have hCclosed : IsClosed C := by
    simpa only [vadd_eq_add] using
      (isClosed_Iic : IsClosed (Set.Iic (0 : ι → ℝ))).vadd_left_of_isCompact hK
  have hCconvex : Convex ℝ C := (convex_convexHull ℝ _).add (convex_Iic _)
  have hyK : y ∈ K := subset_convexHull ℝ _ ⟨Equiv.refl ι, rfl⟩
  have hxC : x ∈ C := by
    by_contra hx
    obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point hCconvex hCclosed hx
    have hf0 (i : ι) : 0 ≤ f (Pi.single i 1) := by
      by_contra hi
      have hi : f (Pi.single i 1) < 0 := lt_of_not_ge hi
      let t : ℝ := (|u - f y| + 1) / (-f (Pi.single i 1))
      have ht : 0 ≤ t := by
        dsimp [t]
        exact div_nonneg (by linarith [abs_nonneg (u - f y)]) (by linarith)
      have hw : -t • Pi.single i (1 : ℝ) ≤ (0 : ι → ℝ) := by
        intro j
        by_cases hij : j = i <;> simp [hij, ht]
      have hmem : y + (-t • Pi.single i (1 : ℝ)) ∈ C :=
        Set.add_mem_add hyK hw
      have hlt := hu _ hmem
      have hprod : t * (-f (Pi.single i 1)) = |u - f y| + 1 := by
        dsimp [t]
        exact div_mul_cancel₀ _ (by linarith)
      have he : f (y + (-t • Pi.single i (1 : ℝ))) = f y + t * (-f (Pi.single i 1)) := by
        rw [map_add, map_smul]
        simp only [smul_eq_mul]
        ring
      rw [he, hprod] at hlt
      linarith [le_abs_self (u - f y)]
    obtain ⟨σ, hσ⟩ := hxy.exists_perm_sum_mul_le (fun i => f (Pi.single i 1)) hf0
    have hpK : y ∘ σ ∈ K := subset_convexHull ℝ _ ⟨σ, rfl⟩
    have hpC : y ∘ σ ∈ C := by
      simpa only [add_zero] using Set.add_mem_add hpK
        (Set.mem_Iic.mpr (show (0 : ι → ℝ) ≤ 0 from le_rfl))
    have hle : f x ≤ f (y ∘ σ) := by
      change f.toLinearMap x ≤ f.toLinearMap (y ∘ σ)
      rw [apply_eq_sum_mul_single f.toLinearMap x, apply_eq_sum_mul_single f.toLinearMap (y ∘ σ)]
      exact hσ
    exact (hle.trans_lt (hu _ hpC)).not_gt hux
  rcases hxC with ⟨z, hz, w, hw, hzw⟩
  refine ⟨z, ?_, (majorized_iff_mem_convexHull_permutations z y).mpr hz⟩
  rw [← hzw]
  exact add_le_of_nonpos_right hw

/-- Weak majorization implies the sum inequality for every increasing convex
real function, with no sign condition on the vectors.
Marshall–Olkin–Arnold (2011), Proposition 4.B.2.
atlas: majorization-def (partial) -/
theorem WeaklyMajorized.sum_monotone_convex_le {x y : ι → ℝ} (hxy : WeaklyMajorized x y)
    {φ : ℝ → ℝ} (hφm : Monotone φ) (hφ : ConvexOn ℝ Set.univ φ) :
    (∑ i, φ (x i)) ≤ ∑ i, φ (y i) := by
  obtain ⟨z, hxz, hzy⟩ := hxy.exists_le_majorized
  exact (Finset.sum_le_sum fun i _ => hφm (hxz i)).trans (hzy.sum_convex_le hφ)

/-- Every translated positive-part function is increasing and convex. -/
theorem monotone_convexOn_max_sub (a : ℝ) :
    Monotone (fun u : ℝ => max (u - a) 0) ∧ ConvexOn ℝ Set.univ (fun u : ℝ => max (u - a) 0) := by
  refine ⟨fun u v huv => max_le_max (sub_le_sub_right huv a) le_rfl, ?_⟩
  convert
    ((convexOn_id (convex_univ : Convex ℝ (Set.univ : Set ℝ))).add_const (-a)).sup
      (convexOn_const (0 : ℝ) convex_univ) using 1
  all_goals (ext; rfl)

/-- Full weak-majorization equivalence with all increasing convex scalar sum
tests. Includes signed vectors, ties, zero prefixes and empty index types.
Marshall–Olkin–Arnold (2011), Proposition 4.B.2.
atlas: majorization-def (partial) -/
theorem weaklyMajorized_iff_sum_monotone_convex_le (x y : ι → ℝ) :
    WeaklyMajorized x y ↔ ∀ φ : ℝ → ℝ, Monotone φ → ConvexOn ℝ Set.univ φ →
      (∑ i, φ (x i)) ≤ ∑ i, φ (y i) := by
  constructor
  · intro h φ hm hc
    exact h.sum_monotone_convex_le hm hc
  · intro h
    apply weaklyMajorized_of_sum_max_sub_le
    intro a
    exact h _ (monotone_convexOn_max_sub a).1 (monotone_convexOn_max_sub a).2

/-- Full ordinary-majorization equivalence with all convex scalar sum tests.
The affine tests `u` and `-u` recover equality of totals.
Marshall–Olkin–Arnold (2011), Proposition 4.B.1.
atlas: majorization-def (partial) -/
theorem majorized_iff_sum_convex_le (x y : ι → ℝ) :
    Majorized x y ↔ ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ →
      (∑ i, φ (x i)) ≤ ∑ i, φ (y i) := by
  constructor
  · intro h φ hc
    exact h.sum_convex_le hc
  · intro h
    refine ⟨weaklyMajorized_of_sum_max_sub_le (fun a =>
      h _ (monotone_convexOn_max_sub a).2), ?_⟩
    have hpos := h id (convexOn_id convex_univ)
    have hneg := h (fun u : ℝ => -u) (concaveOn_id convex_univ).neg
    simp only [id_eq, Finset.sum_neg_distrib] at hpos hneg
    linarith

end NLAlib
