import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Quantitative finite cardinal-product comparisons

Two nearby grid nodes force a small numerator factor in every cardinal. A point
far from all grid nodes gives the corresponding denominator-free lower comparison.
Helper for `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Polynomial Finset

namespace NLAlib

/-- A small adjacent gap bounds every cardinal by its value at a point far from the grid.
Source: focused reroutes, the quantitative boundary estimate. The assertion is a finite
product inequality and does not require a global interpolation comparison theorem. -/
theorem abs_eval_lagrange_basis_le_gap_mul {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) {a b j : ι} {x y δ B r : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hj : j ∈ s)
    (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hr : 0 < r)
    (hxa : |x - v a| ≤ δ) (hxb : |x - v b| ≤ δ)
    (hxB : ∀ k ∈ s, |x - v k| ≤ B) (hyr : ∀ k ∈ s, r ≤ |y - v k|) :
    |(Lagrange.basis s v j).eval x| ≤
      (δ * B ^ (s.card - 2) / r ^ (s.card - 1)) * |(Lagrange.basis s v j).eval y| := by
  have hk : ∃ k ∈ s.erase j, |x - v k| ≤ δ := by
    by_cases hja : j = a
    · exact ⟨b, mem_erase.mpr ⟨(by simpa [hja] using hab.symm), hb⟩, hxb⟩
    · exact ⟨a, mem_erase.mpr ⟨Ne.symm hja, ha⟩, hxa⟩
  obtain ⟨k, hk, hkδ⟩ := hk
  have hcard : ((s.erase j).erase k).card = s.card - 2 := by
    rw [card_erase_of_mem hk, card_erase_of_mem hj]
    omega
  have hnumx : (∏ l ∈ s.erase j, |x - v l|) ≤ δ * B ^ (s.card - 2) := by
    rw [← mul_prod_erase _ _ hk]
    have hrest : (∏ l ∈ (s.erase j).erase k, |x - v l|) ≤ B ^ (s.card - 2) := by
      calc
        _ ≤ ∏ _l ∈ (s.erase j).erase k, B :=
          prod_le_prod (fun _ _ => abs_nonneg _) (fun l hl =>
            hxB l (mem_of_mem_erase (mem_of_mem_erase hl)))
        _ = _ := by rw [prod_const, hcard]
    exact mul_le_mul hkδ hrest (prod_nonneg (fun _ _ => abs_nonneg _)) hδ
  have hnumy : r ^ (s.card - 1) ≤ ∏ l ∈ s.erase j, |y - v l| := by
    calc
      _ = ∏ _l ∈ s.erase j, r := by rw [prod_const, card_erase_of_mem hj]
      _ ≤ _ := prod_le_prod (fun _ _ => hr.le)
        (fun l hl => hyr l (mem_of_mem_erase hl))
  let D : ℝ := ∏ l ∈ s.erase j, |(v j - v l)⁻¹|
  have hD : 0 ≤ D := prod_nonneg (fun _ _ => abs_nonneg _)
  have hval (z : ℝ) : |(Lagrange.basis s v j).eval z| = D * ∏ l ∈ s.erase j, |z - v l| := by
    simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_mul, eval_C,
      eval_sub, eval_X, abs_prod, abs_mul, prod_mul_distrib, D]
  rw [hval x, hval y]
  calc
    _ ≤ D * (δ * B ^ (s.card - 2)) := mul_le_mul_of_nonneg_left hnumx hD
    _ = (δ * B ^ (s.card - 2) / r ^ (s.card - 1)) * (D * r ^ (s.card - 1)) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnumy hD) (by positivity)

end NLAlib
