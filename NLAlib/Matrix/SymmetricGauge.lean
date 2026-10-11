import NLAlib.Matrix.MajorizationConvex
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Convex.Combination

/-!
# Symmetric gauges and majorization dominance

A symmetric gauge is a genuine real-vector norm invariant under permutations
and coordinate signs. The dominance proof uses the full HLP permutation hull
and the convex hull of the sign vertices of a coordinate box. No norming
functional, gauge dominance or matrix norm theorem is assumed.
Source: Bhatia (1997), Theorems IV.2.1–IV.2.2.
Atlas: `unitarily-invariant-norm-def`.
-/

noncomputable section
open scoped BigOperators

namespace NLAlib

/-- A symmetric gauge on a finite real coordinate space, stated in Mathlib's
bundled seminorm vocabulary with an explicit separating zero criterion.
Bhatia (1997), §IV.2.
atlas: unitarily-invariant-norm-def (partial) -/
structure SymmetricGauge (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The underlying absolutely homogeneous, subadditive real seminorm. -/
  seminorm : Seminorm ℝ (ι → ℝ)
  /-- The seminorm separates zero, so it is a genuine norm. -/
  eq_zero_of_map_eq_zero : ∀ x, seminorm x = 0 → x = 0
  /-- Coordinate permutations preserve the norm. -/
  permutation_invariant : ∀ (x : ι → ℝ) (σ : Equiv.Perm ι), seminorm (x ∘ σ) = seminorm x
  /-- Independent unit real signs preserve the norm. -/
  sign_invariant : ∀ (x ε : ι → ℝ), (∀ i, |ε i| = 1) →
    seminorm (fun i => ε i * x i) = seminorm x

namespace SymmetricGauge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : SymmetricGauge ι)

/-- The scalar gauge evaluated on a vector. This is the underlying Mathlib seminorm. -/
def value (x : ι → ℝ) : ℝ := Φ.seminorm x

/-- A gauge sublevel set is convex. -/
theorem convex_sublevel (c : ℝ) : Convex ℝ {x : ι → ℝ | Φ.value x ≤ c} := by
  simpa only [Set.sep_univ, value] using Φ.seminorm.convexOn.convex_le c

/-- A symmetric gauge decreases under ordinary majorization. The proof uses
the actual permutation convex hull from the full HLP characterization. -/
theorem value_le_of_majorized {x y : ι → ℝ} (hxy : Majorized x y) : Φ.value x ≤ Φ.value y := by
  apply convexHull_min (s := Set.range fun σ : Equiv.Perm ι => y ∘ σ)
    (t := {x : ι → ℝ | Φ.value x ≤ Φ.value y}) _ (Φ.convex_sublevel _) hxy.mem_convexHull_permutations
  rintro z ⟨σ, rfl⟩
  exact (Φ.permutation_invariant y σ).le

/-- A gauge norm is monotone on the nonnegative coordinate orthant. The box
between independent sign vertices is their actual convex hull. -/
theorem value_le_of_nonneg_of_le {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ i, 0 ≤ y i) (hxy : x ≤ y) : Φ.value x ≤ Φ.value y := by
  classical
  let V : Set (ι → ℝ) := Set.univ.pi (fun i => ({-y i, y i} : Set ℝ))
  have hxV : x ∈ convexHull ℝ V := by
    apply mem_convexHull_pi
    intro i _
    rw [convexHull_pair, segment_eq_Icc (show -y i ≤ y i by linarith [hy i])]
    exact ⟨by linarith [hx i, hy i], hxy i⟩
  have hV : V ⊆ {z : ι → ℝ | Φ.value z ≤ Φ.value y} := by
    intro z hz
    let ε : ι → ℝ := fun i => if z i = y i then 1 else -1
    have heps (i : ι) : |ε i| = 1 := by dsimp [ε]; split <;> norm_num
    have hzε : z = fun i => ε i * y i := by
      funext i
      have hi := hz i (Set.mem_univ i)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with hi | hi
      · dsimp [ε]
        split_ifs with h
        · simpa using h
        · simpa using hi
      · simp [ε, hi]
    rw [hzε]
    exact (Φ.sign_invariant y ε heps).le
  exact convexHull_min hV (Φ.convex_sublevel _) hxV

/-- Full gauge dominance under weak majorization of nonnegative vectors.
Coordinate domination followed by ordinary majorization handles the weak total.
Bhatia (1997), Theorem IV.2.2.
atlas: unitarily-invariant-norm-def (partial) -/
theorem value_le_of_weaklyMajorized {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hxy : WeaklyMajorized x y) : Φ.value x ≤ Φ.value y := by
  obtain ⟨z, hxz, hzy⟩ := hxy.exists_le_majorized
  have hz (i : ι) : 0 ≤ z i := (hx i).trans (hxz i)
  exact (Φ.value_le_of_nonneg_of_le hx hz hxz).trans (Φ.value_le_of_majorized hzy)

/-- Coordinate absolute values leave a symmetric gauge unchanged. -/
theorem value_abs (x : ι → ℝ) : Φ.value (fun i => |x i|) = Φ.value x := by
  classical
  let ε : ι → ℝ := fun i => if 0 ≤ x i then 1 else -1
  have heps (i : ι) : |ε i| = 1 := by dsimp [ε]; split <;> norm_num
  have h : (fun i => |x i|) = fun i => ε i * x i := by
    funext i
    dsimp [ε]
    split_ifs with hi
    · simp [abs_of_nonneg hi]
    · simp [abs_of_neg (lt_of_not_ge hi)]
  rw [h]
  exact Φ.sign_invariant x ε heps

end SymmetricGauge
end NLAlib
