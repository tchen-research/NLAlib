import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Summing coordinate moduli on finite products

A modulus for changes in one coordinate telescopes to the sum of the coordinate
moduli on the whole Cartesian product. No differentiability is needed.
-/

noncomputable section

open Finset Set

namespace Function

/-- Bounds for one-coordinate changes imply the corresponding summed bound
for arbitrary pairs in a finite Cartesian product. -/
theorem abs_sub_le_sum_of_coordinate_bound {ι : Type*} [Fintype ι]
    (S : ι → Set ℝ) (f : (ι → ℝ) → ℝ) (L : ι → ℝ)
    (hf : ∀ i, ∀ x, (∀ j, x j ∈ S j) → ∀ y, (∀ j, y j ∈ S j) →
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ L i * |x i - y i|)
    {x y : ι → ℝ} (hx : ∀ j, x j ∈ S j) (hy : ∀ j, y j ∈ S j) :
    |f x - f y| ≤ ∑ i, L i * |x i - y i| := by
  classical
  let z (s : Finset ι) : ι → ℝ := fun i => if i ∈ s then x i else y i
  have hz (s : Finset ι) : ∀ j, z s j ∈ S j := by
    intro j
    dsimp [z]
    split_ifs
    · exact hx j
    · exact hy j
  have h (s : Finset ι) : |f (z s) - f y| ≤ ∑ i ∈ s, L i * |x i - y i| := by
    induction s using Finset.induction_on with
    | empty => simp [z]
    | @insert i s hi ih =>
      have hcoord := hf i (z (insert i s)) (hz _) (z s) (hz _) (by
        intro j hji
        simp [z, hji])
      simp only [z, mem_insert_self, if_true, if_neg hi] at hcoord
      rw [sum_insert hi]
      exact (abs_sub_le (f (z (insert i s))) (f (z s)) (f y)).trans (add_le_add hcoord ih)
  simpa only [z, Finset.mem_univ, if_true] using h univ

end Function
