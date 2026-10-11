/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyAnalysisOperators

set_option autoImplicit false

/-!
# Heavy creation occupation-energy estimate

The creation analysis energy bound by total occupation-weighted input energy.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- The summed `A_r` energy is bounded by the total occupation-number
quadratic form, on the literal pattern basis.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUp_energy_le_weighted (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    (∑ r, fockNormSq (Matrix.mulVec (AUpMatrix F r) x)) ≤
      ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
  classical
  calc
    (∑ r, fockNormSq (Matrix.mulVec (AUpMatrix F r) x)) =
        ∑ r, ∑ σ,
          (∑ i ∈ σ.heavyInRow r,
            analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      simp only [fockNormSq, AUpMatrix_mulVec]
    _ ≤ ∑ r, ∑ σ,
        ((σ.heavyInRow r).card : ℝ) *
          ∑ i ∈ σ.heavyInRow r,
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro σ _
      exact sq_sum_le_card_mul_sum_sq
    _ = ∑ σ, ∑ r,
        ((σ.heavyInRow r).card : ℝ) *
          ∑ i ∈ σ.heavyInRow r,
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ σ, ∑ r, ∑ i ∈ σ.heavyInRow r,
        ((σ.heavyInRow r).card : ℝ) *
          (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ = ∑ z : MarkedSite m n .two,
        ((z.pattern.heavyInRow z.row).card : ℝ) *
          (analyze F
            (fiber x (setSite z.pattern (z.row, z.col) .one)) z.col) ^ 2 := by
      simpa only [Pattern.heavyInRow] using
        sum_markedSite (m := m) (n := n) .two
          (fun σ r i ↦ ((σ.heavyInRow r).card : ℝ) *
            (analyze F (fiber x (setSite σ (r, i) .one)) i) ^ 2)
    _ = ∑ z : MarkedSite m n .one,
        ((((setSite z.pattern (z.row, z.col) .two).heavyInRow z.row).card : ℕ) : ℝ) *
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      rw [sum_marked_reindex .two .one]
      apply Finset.sum_congr rfl
      intro z _
      simp only [markedTransition, Equiv.coe_fn_symm_mk]
      rw [setSite_restore z.pattern (z.row, z.col) z.state]
    _ ≤ ∑ z : MarkedSite m n .one,
        (rowGrade z.pattern z.row : ℝ) *
          (analyze F (fiber x z.pattern) z.col) ^ 2 := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_heavy_after_promote_le_rowGrade z.state)
        (sq_nonneg _)
    _ = ∑ p, ∑ r, ∑ i ∈ p.lightInRow r,
        (rowGrade p r : ℝ) * (analyze F (fiber x p) i) ^ 2 := by
      symm
      simpa only [Pattern.lightInRow] using
        sum_markedSite (m := m) (n := n) .one
          (fun p r i ↦ (rowGrade p r : ℝ) *
            (analyze F (fiber x p) i) ^ 2)
    _ = ∑ p, ∑ r, (rowGrade p r : ℝ) *
        ∑ i ∈ p.lightInRow r, (analyze F (fiber x p) i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    _ ≤ ∑ p, ∑ r, (rowGrade p r : ℝ) *
        ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (subset_analysis F (p.lightInRow r) (fiber x p)) (Nat.cast_nonneg _)
    _ = ∑ p, (p.grade : ℝ) * ParsevalFrame.normSq (fiber x p) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_mul]
      norm_cast
      rw [sum_rowGrade]

end

end NLAlib.SparseFock.HeavyBandsConcrete
